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

def rotl(value, rotation, wordsize):
    if rotation % wordsize == 0:
        return "{0}".format(value)
    command = "((({0} << {1})[{2}:0]) | (({0} >> {3})[{2}:0]))".format(
        value, (rotation % wordsize), wordsize - 1, (wordsize - rotation) % wordsize)

    return command
    
def rotr(value, rotation, wordsize):
    if rotation % wordsize == 0:
        return "{0}".format(value)
    command = "((({0} >> {1})[{2}:0]) | (({0} << {3})[{2}:0]))".format(
        value, (rotation % wordsize), wordsize - 1, (wordsize - rotation) % wordsize)
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

# ====== LBlock cipher commands
class Diff_LBlock_CVC_Cipher:

    def createSTP(self, stp_filename, parameters):
        """
        Creates an STP file to find a characteristic for LBlock with
        the given parameters.
        """

        wordsize = parameters["wordsize"]
        rounds = parameters["rounds"]
        weight = parameters["weight"]

        with open(stp_filename, 'w') as stp_file:
            header = ("% Input File for STP\n% LBlock w={}"
                      "rounds={}\n\n\n".format(wordsize,rounds))
            stp_file.write(header)

            # Setup variables
            # x = left, y = right
            x = ["X{}".format(i) for i in range(rounds + 1)]
            y = ["Y{}".format(i) for i in range(rounds + 1)]
            f_out = ["fout{}".format(i) for i in range(rounds + 1)]
            s_out = ["sout{}".format(i) for i in range(rounds + 1)]

            # w = weight
            w = ["w{}".format(i) for i in range(rounds)]

            setupVariables(stp_file, x, wordsize)
            setupVariables(stp_file, y, wordsize)
            setupVariables(stp_file, f_out, wordsize)
            setupVariables(stp_file, s_out, wordsize)
            setupVariables(stp_file, w, wordsize)

            setupWeightComputation(stp_file, weight, w, wordsize)

            for i in range(rounds):
                self.setupLBlockRound(stp_file, x[i], y[i], x[i+1], y[i+1], f_out[i], s_out[i], w[i], wordsize)

            # No all zero characteristic
            assertNonZero(stp_file, x+y, wordsize)

            setupQuery(stp_file)

        return

    def setupLBlockRound(self, stp_file, x_in, y_in, x_out, y_out, f_out, s_out, w, wordsize):
        """
        Model for differential behaviour of one round LBlock
        y[i+1] = x[i]
        x[i+1] = P(S(x[i])) xor y[i] <<< 8
        """
        command = ""

        #Assert(y[i+1] = x[i])
        command += "ASSERT({} = {});\n".format(y_out, x_in)

        y_in_rot = rotl(y_in, 8, wordsize)
        
        command += self.F(x_in, s_out, f_out, w)

        #Assert XOR
        command += diff_Xor_CVC(f_out, y_in_rot, x_out, wordsize)
        # command += "ASSERT({} = BVXOR({}, {}));\n".format(x_out, f_out, y_in_rot)

        stp_file.write(command)
        return
    
    def F(self, f_in, s_out, f_out, w):
        """
        Model for the F function used in LBlock
        """
        command = ""

        # Substitution Layer
        s0 = [0xE, 9, 0xF, 0, 0xD, 4, 0xA, 0xB, 1, 2, 8, 3, 7, 6, 0xC, 5]
        s1 = [4, 0xB, 0xE, 9, 0xF, 0xD, 0, 0xA, 7, 0xC, 5, 6, 2, 8, 1, 3]
        s2 = [1, 0xE, 7, 0xC, 0xF, 0xD, 0, 6, 0xB, 5, 9, 3, 2, 4, 8, 0xA]
        s3 = [7, 6, 8, 0xB, 0, 0xF, 3, 0xE, 9, 0xA, 0xC, 0xD, 5, 2, 4, 1]
        s4 = [0xE, 5, 0xF, 0, 7, 2, 0xC, 0xD, 1, 8, 4, 9, 0xB, 0xA, 6, 3]
        s5 = [2, 0xD, 0xB, 0xC, 0xF, 0xE, 0, 9, 7, 0xA, 6, 3, 1, 8, 4, 5]
        s6 = [0xB, 9, 4, 0xE, 0, 0xF, 0xA, 0xD, 6, 0xC, 5, 7, 3, 8, 1, 2]
        s7 = [0xD, 0xA, 0xF, 0, 0xE, 4, 9, 0xB, 2, 1, 8, 3, 7, 5, 0xC, 6]

        #s0
        variables = ["{0}[{1}:{1}]".format(f_in, 3),
                     "{0}[{1}:{1}]".format(f_in, 2),
                     "{0}[{1}:{1}]".format(f_in, 1),
                     "{0}[{1}:{1}]".format(f_in, 0),
                     "{0}[{1}:{1}]".format(s_out, 3),
                     "{0}[{1}:{1}]".format(s_out, 2),
                     "{0}[{1}:{1}]".format(s_out, 1),
                     "{0}[{1}:{1}]".format(s_out, 0),
                     "{0}[{1}:{1}]".format(w, 3),
                     "{0}[{1}:{1}]".format(w, 2),
                     "{0}[{1}:{1}]".format(w, 1),
                     "{0}[{1}:{1}]".format(w, 0)]
        command += add4bitSbox_CVC(s0, variables)

        #s1
        variables = ["{0}[{1}:{1}]".format(f_in, 7),
                     "{0}[{1}:{1}]".format(f_in, 6),
                     "{0}[{1}:{1}]".format(f_in, 5),
                     "{0}[{1}:{1}]".format(f_in, 4),
                     "{0}[{1}:{1}]".format(s_out, 7),
                     "{0}[{1}:{1}]".format(s_out, 6),
                     "{0}[{1}:{1}]".format(s_out, 5),
                     "{0}[{1}:{1}]".format(s_out, 4),
                     "{0}[{1}:{1}]".format(w, 7),
                     "{0}[{1}:{1}]".format(w, 6),
                     "{0}[{1}:{1}]".format(w, 5),
                     "{0}[{1}:{1}]".format(w, 4)]
        command += add4bitSbox_CVC(s1, variables)

        #s2
        variables = ["{0}[{1}:{1}]".format(f_in, 11),
                     "{0}[{1}:{1}]".format(f_in, 10),
                     "{0}[{1}:{1}]".format(f_in, 9),
                     "{0}[{1}:{1}]".format(f_in, 8),
                     "{0}[{1}:{1}]".format(s_out, 11),
                     "{0}[{1}:{1}]".format(s_out, 10),
                     "{0}[{1}:{1}]".format(s_out, 9),
                     "{0}[{1}:{1}]".format(s_out, 8),
                     "{0}[{1}:{1}]".format(w, 11),
                     "{0}[{1}:{1}]".format(w, 10),
                     "{0}[{1}:{1}]".format(w, 9),
                     "{0}[{1}:{1}]".format(w, 8)]
        command += add4bitSbox_CVC(s2, variables)

        #s3
        variables = ["{0}[{1}:{1}]".format(f_in, 15),
                     "{0}[{1}:{1}]".format(f_in, 14),
                     "{0}[{1}:{1}]".format(f_in, 13),
                     "{0}[{1}:{1}]".format(f_in, 12),
                     "{0}[{1}:{1}]".format(s_out, 15),
                     "{0}[{1}:{1}]".format(s_out, 14),
                     "{0}[{1}:{1}]".format(s_out, 13),
                     "{0}[{1}:{1}]".format(s_out, 12),
                     "{0}[{1}:{1}]".format(w, 15),
                     "{0}[{1}:{1}]".format(w, 14),
                     "{0}[{1}:{1}]".format(w, 13),
                     "{0}[{1}:{1}]".format(w, 12)]
        command += add4bitSbox_CVC(s3, variables)

        #s4
        variables = ["{0}[{1}:{1}]".format(f_in, 19),
                     "{0}[{1}:{1}]".format(f_in, 18),
                     "{0}[{1}:{1}]".format(f_in, 17),
                     "{0}[{1}:{1}]".format(f_in, 16),
                     "{0}[{1}:{1}]".format(s_out, 19),
                     "{0}[{1}:{1}]".format(s_out, 18),
                     "{0}[{1}:{1}]".format(s_out, 17),
                     "{0}[{1}:{1}]".format(s_out, 16),
                     "{0}[{1}:{1}]".format(w, 19),
                     "{0}[{1}:{1}]".format(w, 18),
                     "{0}[{1}:{1}]".format(w, 17),
                     "{0}[{1}:{1}]".format(w, 16)]
        command += add4bitSbox_CVC(s4, variables)

        #s5
        variables = ["{0}[{1}:{1}]".format(f_in, 23),
                     "{0}[{1}:{1}]".format(f_in, 22),
                     "{0}[{1}:{1}]".format(f_in, 21),
                     "{0}[{1}:{1}]".format(f_in, 20),
                     "{0}[{1}:{1}]".format(s_out, 23),
                     "{0}[{1}:{1}]".format(s_out, 22),
                     "{0}[{1}:{1}]".format(s_out, 21),
                     "{0}[{1}:{1}]".format(s_out, 20),
                     "{0}[{1}:{1}]".format(w, 23),
                     "{0}[{1}:{1}]".format(w, 22),
                     "{0}[{1}:{1}]".format(w, 21),
                     "{0}[{1}:{1}]".format(w, 20)]
        command += add4bitSbox_CVC(s5, variables)

        #s6
        variables = ["{0}[{1}:{1}]".format(f_in, 27),
                     "{0}[{1}:{1}]".format(f_in, 26),
                     "{0}[{1}:{1}]".format(f_in, 25),
                     "{0}[{1}:{1}]".format(f_in, 24),
                     "{0}[{1}:{1}]".format(s_out, 27),
                     "{0}[{1}:{1}]".format(s_out, 26),
                     "{0}[{1}:{1}]".format(s_out, 25),
                     "{0}[{1}:{1}]".format(s_out, 24),
                     "{0}[{1}:{1}]".format(w, 27),
                     "{0}[{1}:{1}]".format(w, 26),
                     "{0}[{1}:{1}]".format(w, 25),
                     "{0}[{1}:{1}]".format(w, 24)]
        command += add4bitSbox_CVC(s6, variables)

        #s7
        variables = ["{0}[{1}:{1}]".format(f_in, 31),
                     "{0}[{1}:{1}]".format(f_in, 30),
                     "{0}[{1}:{1}]".format(f_in, 29),
                     "{0}[{1}:{1}]".format(f_in, 28),
                     "{0}[{1}:{1}]".format(s_out, 31),
                     "{0}[{1}:{1}]".format(s_out, 30),
                     "{0}[{1}:{1}]".format(s_out, 29),
                     "{0}[{1}:{1}]".format(s_out, 28),
                     "{0}[{1}:{1}]".format(w, 31),
                     "{0}[{1}:{1}]".format(w, 30),
                     "{0}[{1}:{1}]".format(w, 29),
                     "{0}[{1}:{1}]".format(w, 28)]
        command += add4bitSbox_CVC(s7, variables)

        # Permutation Layer
        command += "ASSERT({0}[7:4] = {1}[3:0]);\n".format(s_out, f_out)
        command += "ASSERT({0}[15:12] = {1}[7:4]);\n".format(s_out, f_out)
        command += "ASSERT({0}[3:0] = {1}[11:8]);\n".format(s_out, f_out)
        command += "ASSERT({0}[11:8] = {1}[15:12]);\n".format(s_out, f_out)

        command += "ASSERT({0}[23:20] = {1}[19:16]);\n".format(s_out, f_out)
        command += "ASSERT({0}[31:28] = {1}[23:20]);\n".format(s_out, f_out)
        command += "ASSERT({0}[19:16] = {1}[27:24]);\n".format(s_out, f_out)
        command += "ASSERT({0}[27:24] = {1}[31:28]);\n".format(s_out, f_out)

        return command 
#####################


def main():
    """
    Parse the arguments and start the request functionality with the provided
    parameters.
    """
    Initial = {"cipher" : "diff_LBlock_CVC",
              "rounds" : 29,
              "wordsize" : 32,
              "weight" : 131,
              "endRound" : 33,
            }

    checkenviroment()
    cipher_suite = Diff_LBlock_CVC_Cipher()

    searchCharacteristics(cipher_suite, Initial)
    
if __name__ == '__main__':
    main()
    
