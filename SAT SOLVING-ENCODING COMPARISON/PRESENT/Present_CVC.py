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

    result = subprocess.check_output(["/home/user/Programs/stp/build/stp", "--exit-after-CNF", "--output-CNF", stp_file, "--CVC", "--disable-simplifications"])
    os.system("cp output_0.cnf tmp_CVC_pure/output_{0}_{1}.cnf".format(parameters["rounds"], parameters["weight"]))
    os.system("rm -f output_{0}_{1}.cnf".format(parameters["rounds"], parameters["weight"]))
    
    #---------------
    time_start = time.time()

    order = "/home/user/Programs/cadical/build/cadical " + "tmp_CVC_pure/output_{0}_{1}.cnf > tmp_CVC_pure/solution_{0}_{1}.out".format(parameters["rounds"], parameters["weight"])
   

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

# def rotl(value, rotation, wordsize):
#     if rotation % wordsize == 0:
#         return "{0}".format(value)
#     command = "((({0} << {1})[{2}:0]) | (({0} >> {3})[{2}:0]))".format(
#         value, (rotation % wordsize), wordsize - 1, (wordsize - rotation) % wordsize)

#     return command
    
# def rotr(value, rotation, wordsize):
#     if rotation % wordsize == 0:
#         return "{0}".format(value)
#     command = "((({0} >> {1})[{2}:0]) | (({0} << {3})[{2}:0]))".format(
#         value, (rotation % wordsize), wordsize - 1, (wordsize - rotation) % wordsize)
#     return command

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

# def diff_Xor_CVC(self,a, b, c, wordsize):
    
#     command = "ASSERT(" + a + " = "
#     command += "BVXOR(" + b + ","
#     command += c
#     command += "));\n"
#     return command

# ====== Present cipher commands
class Diff_Present_CVC_Cipher:

    def createSTP(self, stp_filename, parameters):
        """
        Creates an STP file to find a characteristic for PRESENT with
        the given parameters.
        """

        wordsize = parameters["wordsize"]
        rounds = parameters["rounds"]
        weight = parameters["weight"]
        if wordsize != 64:
            print("Only wordsize of 64-bit supported.")
            exit(1)
            
        with open(stp_filename, 'w') as stp_file:
            header = ("% Input File for STP\n% PRESENT wordsize={} rounds={}\n\n\n".format(wordsize, rounds))
            stp_file.write(header)

            # Setup variables
            s = ["S{}".format(i) for i in range(rounds + 1)]
            p = ["P{}".format(i) for i in range(rounds)]

            # w = weight
            w = ["w{}".format(i) for i in range(rounds)]

            setupVariables(stp_file, s, wordsize)
            setupVariables(stp_file, p, wordsize)
            setupVariables(stp_file, w, wordsize)

            setupWeightComputation(stp_file, weight, w, wordsize)

            for i in range(rounds):
                self.setupPresentRound(stp_file, s[i], p[i], s[i+1], w[i], wordsize)

            # No all zero characteristic
            assertNonZero(stp_file, s, wordsize)


            setupQuery(stp_file)

        return

    def setupPresentRound(self, stp_file, s_in, p, s_out, w, wordsize):
        """
        Model for differential behaviour of one round PRESENT
        """
        command = ""

        #Permutation Layer
        for i in range(16):
            command += "ASSERT({0}[{1}:{1}] = {2}[{3}:{3}]);\n".format(p, i*4+0, s_out, i)
            command += "ASSERT({0}[{1}:{1}] = {2}[{3}:{3}]);\n".format(p, i*4+1, s_out, i+16)
            command += "ASSERT({0}[{1}:{1}] = {2}[{3}:{3}]);\n".format(p, i*4+2, s_out, i+32)
            command += "ASSERT({0}[{1}:{1}] = {2}[{3}:{3}]);\n".format(p, i*4+3, s_out, i+48)

        # Substitution Layer
        present_sbox = [0xc, 5, 6, 0xb, 9, 0, 0xa, 0xd, 3, 0xe, 0xf, 8, 4, 7, 1, 2]
        for i in range(16):
            variables = ["{0}[{1}:{1}]".format(s_in, 4*i + 3),
                         "{0}[{1}:{1}]".format(s_in, 4*i + 2),
                         "{0}[{1}:{1}]".format(s_in, 4*i + 1),
                         "{0}[{1}:{1}]".format(s_in, 4*i + 0),
                         "{0}[{1}:{1}]".format(p, 4*i + 3),
                         "{0}[{1}:{1}]".format(p, 4*i + 2),
                         "{0}[{1}:{1}]".format(p, 4*i + 1),
                         "{0}[{1}:{1}]".format(p, 4*i + 0),
                         "{0}[{1}:{1}]".format(w, 4*i + 3),
                         "{0}[{1}:{1}]".format(w, 4*i + 2),
                         "{0}[{1}:{1}]".format(w, 4*i + 1),
                         "{0}[{1}:{1}]".format(w, 4*i + 0)]
            command += add4bitSbox_CVC(present_sbox, variables)


        stp_file.write(command)
        return
#####################


def main():
    """
    Parse the arguments and start the request functionality with the provided
    parameters.
    """
    Initial = {"cipher" : "diff_Present_CVC",
              "rounds" : 25,
              "wordsize" : 64,
              "weight" : 106,
              "endRound" : 32,
            }

    checkenviroment()
    cipher_suite = Diff_Present_CVC_Cipher()

    searchCharacteristics(cipher_suite, Initial)
    
if __name__ == '__main__':
    main()
    
