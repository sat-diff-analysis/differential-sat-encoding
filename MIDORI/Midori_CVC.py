'''

'''

import subprocess
import random
import math
import os
import time
import itertools

# ======= 
def checkenviroment():
    """

    """

    if not os.path.exists("./tmp_CVC_pure/"):
        os.makedirs("./tmp_CVC_pure/")

    return
# ======= 
def findMinWeightCharacteristic(cipher, parameters):
    """

    """

    print("---")

    start_time = time.time()

    print("round: {} Weight: {}".format(parameters["rounds"], parameters["weight"]))
    # Construct problem instance for given parameters
    stp_file = "tmp_CVC_pure/{}{}_{}_{}.stp".format(parameters["cipher"],
                                     parameters["wordsize"], parameters["rounds"], parameters["weight"])
    cipher.createSTP(stp_file, parameters)
    
    result = ""

    result = solve_SAT_solver(stp_file, parameters)

    while not result:    
        # current_time = round(time.time() - start_time, 2)    
        parameters["weight"] += 1
        print("round: {} Weight: {}".format(parameters["rounds"], parameters["weight"]))
        # Construct problem instance for given parameters
        stp_file = "tmp_CVC_pure/{}{}_{}_{}.stp".format(parameters["cipher"],
                                         parameters["wordsize"], parameters["rounds"], parameters["weight"])
        cipher.createSTP(stp_file, parameters)
        result = solve_SAT_solver(stp_file, parameters)
    

    return parameters["weight"]

def searchCharacteristics(cipher, parameters):
    """

    """
    ##########
    Destance = "tmp_CVC_pure/{}_Speed Test.txt".format(parameters["cipher"])
    d = ""   
    ##########
    # HW_rnd = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
    parameters["time"] = 0
    # e = 0
    while not parameters["endRound"] == (parameters["rounds"] - 1):

        parameters["weight"] = findMinWeightCharacteristic(cipher, parameters)
        d += "Characteristic for Rounds {} Weight {} - Time {}s\n".format(parameters["rounds"], parameters["weight"], parameters["time"])
        with open(Destance, "w") as dec:
            dec.write(d)
        parameters["rounds"] = parameters["rounds"] + 1
        #########11
    #     HW_rnd[e] = parameters["weight"]
    #     if (parameters["rounds"] > 2):
    #         for r in range((int(parameters["rounds"]/2)) - 1):
    #             if ((HW_rnd[r] + HW_rnd[parameters["rounds"] - 2 - r]) > parameters["weight"]):
    #                 parameters["weight"] = (HW_rnd[r] + HW_rnd[parameters["rounds"] - 2 - r])
    #     e = e + 1
    # print(HW_rnd)
    dec.close()
    return

def solve_SAT_solver(stp_file, parameters):

    result = subprocess.check_output(["/home/linuxbrew/.linuxbrew/bin/stp", "--exit-after-CNF", "--output-CNF", stp_file, "--CVC", "--disable-simplifications"])
    os.system("cp output_0.cnf tmp_CVC_pure/output_{0}_{1}.cnf".format(parameters["rounds"], parameters["weight"]))
    os.system("rm -f output_{0}_{1}.cnf".format(parameters["rounds"], parameters["weight"]))
    
    #---------------
    time_start = time.time()

    order = "/home/user/cadical-master/build/cadical " + "tmp_CVC_pure/output_{0}_{1}.cnf > tmp_CVC_pure/solution_{0}_{1}.out".format(parameters["rounds"], parameters["weight"])
   

    os.system(order)
    order = "sed -n '/s SATISFIABLE/p' " + "tmp_CVC_pure/solution_{0}_{1}.out > tmp_CVC_pure/SatSolution_{0}_{1}.out".format(parameters["rounds"], parameters["weight"])
    os.system(order)
    order = "sed -n '/s UNSATISFIABLE/p' " + "tmp_CVC_pure/solution_{0}_{1}.out > tmp_CVC_pure/UnsatSolution_{0}_{1}.out".format(parameters["rounds"], parameters["weight"])
    os.system(order)
    satsol = open("tmp_CVC_pure/SatSolution_{0}_{1}.out".format(parameters["rounds"], parameters["weight"]))
    unsatsol = open("tmp_CVC_pure/UnsatSolution_{0}_{1}.out".format(parameters["rounds"], parameters["weight"]))
    satresult = satsol.readlines()
    unsatresult = unsatsol.readlines()
    satsol.close()
    unsatsol.close()
    if ((len(satresult) == 0) and (len(unsatresult) > 0)):
        flag = False
    if ((len(satresult) > 0) and (len(unsatresult) == 0)):
        flag = True
    else:
        flag = False
    order = "rm tmp_CVC_pure/SatSolution_{0}_{1}.out".format(parameters["rounds"], parameters["weight"])
    os.system(order)
    order = "rm tmp_CVC_pure/UnsatSolution_{0}_{1}.out".format(parameters["rounds"], parameters["weight"])
    os.system(order)
    # Removing cnf file
    #order = "rm Problem-Round" + str(Round) + "-Probability" + str(Probability) + ".cnf"
    #os.system(order)
    time_end = time.time()
        # Printing solutions
    if (flag == True):
        print(" Sat; TotalCost: " + str(time_end - time_start))
    else:
        print("Unsat; TotalCost: " + str(time_end - time_start))
        #return flag
    parameters["time"] += (time_end - time_start)
    print("Total_Time: {}".format(parameters["time"]))
    #-----------------
    return flag

# ====== STP commands
def setupQuery(stpfile):
    """
    Adds the query and printing of counterexample to the stp stpfile.
    """
    stpfile.write("QUERY(FALSE);\n")
    stpfile.write("COUNTEREXAMPLE;\n")
    return


def setupVariables(stpfile, variables, wordsize):
    """
    Adds a list of variables to the stp stpfile.
    """
    stpfile.write(getStringForVariables(variables, wordsize) + '\n')
    return


def getStringForVariables(variables, wordsize):
    """
    Takes as input the variable name, number of variables and the wordsize
    and constructs for instance a string of the form:
    x00, x01, ..., x30: BITVECTOR(wordsize);
    """
    command = ""
    for var in variables:
        command += var + ","

    command = command[:-1]
    command += ": BITVECTOR({0});".format(wordsize)
    return command


def assertNonZero(stpfile, variables, wordsize):
    stpfile.write(getStringForNonZero(variables, wordsize) + '\n')
    return

def getStringForNonZero(variables, wordsize):
    """
    Asserts that no all-zero characteristic is allowed
    
    command = "1 2 ... 63 0"
    """
    command = "ASSERT(NOT(("
    for var in variables:
        command += var + "|"

    command = command[:-1]
    command += ") = 0bin{}));".format("0" * wordsize)
    return command

def setupWeightComputation(stpfile, weight, p, wordsize, ignoreMSBs=0):
    """
    Assert that weight is equal to the sum of the hamming weight of p.
    """
    stpfile.write("weight: BITVECTOR(16);\n")
    stpfile.write(getWeightString(p, wordsize, ignoreMSBs) + "\n")
    stpfile.write("ASSERT(weight = {0:#018b});\n".format(weight))
    #stpfile.write("ASSERT(BVLE(weight, {0:#018b}));\n".format(weight))
    return

def getWeightString(variables, wordsize, ignoreMSBs=0, weightVariable="weight"):
    """
    Asserts that the weight is equal to the hamming weight of the
    given variables.
    """
    # if len(variables) == 1:
    #     return "ASSERT({} = {});\n".format(weightVariable, variables[0])

    command = "ASSERT(({} = BVPLUS(16,".format(weightVariable)
    for var in variables:
        tmp = "0b00000000@(BVPLUS(8, "
        for bit in range(wordsize - ignoreMSBs):
            # Ignore MSBs if they do not contribute to
            # probability of the characteristic.
            tmp += "0bin0000000@({0}[{1}:{1}]),".format(var, bit)
        # Pad the constraint if necessary
        if (wordsize - ignoreMSBs) == 1:
            tmp += "0bin0,"
        command += tmp[:-1] + ")),"
    if len(variables):
        command += "0bin0000000000000000,"
    command = command[:-1]
    command += ")));"

    return command



def add4bitSbox_CVC(sbox, variables):
    """

    """
    assert(len(sbox) == 16)
    assert(len(variables) == 12)

    # First compute the DDT
    DDT = [[0]*16 for i in range(16)]

    for a in range(16):
        for b in range(16):
            DDT[a ^ b][sbox[a] ^ sbox[b]] += 1

    # Construct DNF of all valid trails
    trails = []

    # All zero trail with probability 1
    for input_diff in range(16):
        for output_diff in range(16):
            if DDT[input_diff][output_diff] != 0:
                tmp = []
                tmp.append((input_diff >> 3) & 1)
                tmp.append((input_diff >> 2) & 1)
                tmp.append((input_diff >> 1) & 1)
                tmp.append((input_diff >> 0) & 1)
                tmp.append((output_diff >> 3) & 1)
                tmp.append((output_diff >> 2) & 1)
                tmp.append((output_diff >> 1) & 1)
                tmp.append((output_diff >> 0) & 1)
                if DDT[input_diff][output_diff] == 2:
                    tmp += [0, 1, 1, 1] # 2^-3
                elif DDT[input_diff][output_diff] == 4:
                    tmp += [0, 0, 1, 1] # 2^-2
                elif DDT[input_diff][output_diff] == 8:
                    tmp += [0, 0, 0, 1] # 2^-1
                elif DDT[input_diff][output_diff] == 16:
                    tmp += [0, 0, 0, 0]
                trails.append(tmp)

    # Build CNF from invalid trails
    cnf = ""
    for prod in itertools.product([0, 1], repeat=len(trails[0])):
        # Trail is not valid
        if list(prod) not in trails:
            expr = ["~" if x == 1 else "" for x in list(prod)]
            clause = ""
            for literal in range(12):
                clause += "{0}{1} | ".format(expr[literal], variables[literal])

            cnf += "({}) &".format(clause[:-2])

    return "ASSERT({} = 0bin1);\n".format(cnf[:-2])

def diff_Xor_CVC(a, b, c, wordsize):
    
    command = "ASSERT(" + a + " = "
    command += "BVXOR(" + b + ","
    command += c
    command += "));\n"
    return command

# ====== Midori cipher commands
class Diff_Midori_CVC_Cipher:

    def createSTP(self, stp_filename, parameters):
        """
        Creates an STP file to find a characteristic for Midori with
        the given parameters.
        """

        wordsize = parameters["wordsize"]
        rounds = parameters["rounds"]
        weight = parameters["weight"]

        if wordsize != 64:
            print("Only wordsize of 64-bit supported.")
            exit(1)

        with open(stp_filename, 'w') as stp_file:
            header = ("% Input File for STP\n% MIDORI w={}"
                      "rounds={}\n\n\n".format(wordsize, rounds))
            stp_file.write(header)

            # Setup variables
            sb = ["SB{}".format(i) for i in range(rounds + 1)]
            sc = ["SC{}".format(i) for i in range(rounds)]
            mc = ["MC{}".format(i) for i in range(rounds)]

            # w = weight
            w = ["w{}".format(i) for i in range(rounds)]

            setupVariables(stp_file, sb, wordsize)
            setupVariables(stp_file, sc, wordsize)
            setupVariables(stp_file, mc, wordsize)
            setupVariables(stp_file, w, wordsize)

            setupWeightComputation(stp_file, weight, w, wordsize)

            for i in range(rounds):
                self.setupMidoriRound(stp_file, sb[i], sc[i], mc[i], sb[i+1],
                                      w[i], wordsize)

            # No all zero characteristic
            assertNonZero(stp_file, sb, wordsize)

            setupQuery(stp_file)

        return

    def setupMidoriRound(self, stp_file, sb_in, sc, mc, sb_out, w, wordsize):
        """
        Model for differential behaviour of one round MIDORI
        """
        command = ""

        #Permutation Layer

        permutation = [0x0, 0xa, 0x5, 0xf, 0xe, 0x4, 0xb, 0x1,
                       0x9, 0x3, 0xc, 0x6, 0x7, 0xd, 0x2, 0x8]

        for idx, val in enumerate(permutation):
            command += "ASSERT({0}[{1}:{2}] = {3}[{4}:{5}]);\n".format(
                sc, 4*val + 3, 4*val, mc, 4*idx + 3, 4*idx)

        for col in range(4):
            for bit in range(4):
                offset0 = col*16 + 0 + bit
                offset1 = col*16 + 4 + bit
                offset2 = col*16 + 8 + bit
                offset3 = col*16 + 12 + bit

                command += "ASSERT(BVXOR(BVXOR({4}[{1}:{1}], {4}[{2}:{2}]), {4}[{3}:{3}]) \
                             = {5}[{0}:{0}]);\n".format(offset0, offset1, offset2, offset3, mc, sb_out)
                command += "ASSERT(BVXOR(BVXOR({4}[{0}:{0}], {4}[{2}:{2}]), {4}[{3}:{3}]) \
                             = {5}[{1}:{1}]);\n".format(offset0, offset1, offset2, offset3, mc, sb_out)
                command += "ASSERT(BVXOR(BVXOR({4}[{0}:{0}], {4}[{1}:{1}]), {4}[{3}:{3}]) \
                             = {5}[{2}:{2}]);\n".format(offset0, offset1, offset2, offset3, mc, sb_out)
                command += "ASSERT(BVXOR(BVXOR({4}[{0}:{0}], {4}[{1}:{1}]), {4}[{2}:{2}]) \
                             = {5}[{3}:{3}]);\n".format(offset0, offset1, offset2, offset3, mc, sb_out)


        # Substitution Layer
        midori_sbox = [0xc, 0xa, 0xd, 3, 0xe, 0xb, 0xf, 7, 8, 9, 1, 5, 0, 2, 4, 6]
        for i in range(16):
            variables = ["{0}[{1}:{1}]".format(sb_in, 4*i + 3),
                         "{0}[{1}:{1}]".format(sb_in, 4*i + 2),
                         "{0}[{1}:{1}]".format(sb_in, 4*i + 1),
                         "{0}[{1}:{1}]".format(sb_in, 4*i + 0),
                         "{0}[{1}:{1}]".format(sc, 4*i + 3),
                         "{0}[{1}:{1}]".format(sc, 4*i + 2),
                         "{0}[{1}:{1}]".format(sc, 4*i + 1),
                         "{0}[{1}:{1}]".format(sc, 4*i + 0),
                         "{0}[{1}:{1}]".format(w, 4*i + 3),
                         "{0}[{1}:{1}]".format(w, 4*i + 2),
                         "{0}[{1}:{1}]".format(w, 4*i + 1),
                         "{0}[{1}:{1}]".format(w, 4*i + 0)]
            command += add4bitSbox_CVC(midori_sbox, variables)

        stp_file.write(command)
        return

#####################


def main():
    """
    Parse the arguments and start the request functionality with the provided
    parameters.
    """
    Initial = {"cipher" : "diff_Midori_CVC",
              "rounds" : 16,
              "wordsize" : 64,
              "weight" : 150,
              "endRound" : 16,
            }

    checkenviroment()
    cipher_suite = Diff_Midori_CVC_Cipher()

    searchCharacteristics(cipher_suite, Initial)
    
if __name__ == '__main__':
    main()
    
