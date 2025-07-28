'''

'''

import subprocess
import random
import math
import os
import time


# ======= 
def checkenviroment():
    """
    Basic checks if the enviroment is set up correctly
    """

    if not os.path.exists("./tmp_CNF_LF/"):
        os.makedirs("./tmp_CNF_LF/")

    return
# ======= 
def findMinWeightCharacteristic(cipher, parameters):
    """

    """

    print("---")

    start_time = time.time()

    print("round: {} Weight: {}".format(parameters["rounds"], parameters["weight"]))
    # Construct problem instance for given parameters
    stp_file = "tmp_CNF_LF/{}{}_{}_{}.stp".format(parameters["cipher"], parameters["wordsize"], parameters["rounds"], parameters["weight"])
    cipher.createSTP(stp_file, parameters)
    
    result = ""

    result = solve_SAT_solver(stp_file, parameters)

    while not result:
        parameters["weight"] += 1
        print("round: {} Weight: {}".format(parameters["rounds"], parameters["weight"]))
        # Construct problem instance for given parameters
        stp_file = "tmp_CNF_LF/{}{}_{}_{}.stp".format(parameters["cipher"], parameters["wordsize"], parameters["rounds"], parameters["weight"])
        cipher.createSTP(stp_file, parameters)
        result = solve_SAT_solver(stp_file, parameters)
    

    return parameters["weight"]


def searchCharacteristics(cipher, parameters):
    """
    Searches for differential characteristics of minimal weight for an increasing number of rounds.
    """
    ##########
    Destance = "tmp_CNF_LF/{}_Speed Test.txt".format(parameters["cipher"])
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
        #########
    #     HW_rnd[e] = parameters["weight"]
    #     # parameters["Pr_Round"].append(parameters["weight"])
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
    os.system("cp output_0.cnf tmp_CNF_LF/output_{0}_{1}.cnf".format(parameters["rounds"], parameters["weight"]))
    os.system("rm -f output_{0}_{1}.cnf".format(parameters["rounds"], parameters["weight"]))
    
    #---------------
    time_start = time.time()

    order = "/home/user/cadical-master/build/cadical " + "tmp_CNF_LF/output_{0}_{1}.cnf > tmp_CNF_LF/solution_{0}_{1}.out".format(parameters["rounds"], parameters["weight"])
   

    os.system(order)
    order = "sed -n '/s SATISFIABLE/p' " + "tmp_CNF_LF/solution_{0}_{1}.out > tmp_CNF_LF/SatSolution_{0}_{1}.out".format(parameters["rounds"], parameters["weight"])
    os.system(order)
    order = "sed -n '/s UNSATISFIABLE/p' " + "tmp_CNF_LF/solution_{0}_{1}.out > tmp_CNF_LF/UnsatSolution_{0}_{1}.out".format(parameters["rounds"], parameters["weight"])
    os.system(order)
    satsol = open("tmp_CNF_LF/SatSolution_{0}_{1}.out".format(parameters["rounds"], parameters["weight"]))
    unsatsol = open("tmp_CNF_LF/UnsatSolution_{0}_{1}.out".format(parameters["rounds"], parameters["weight"]))
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
    order = "rm tmp_CNF_LF/SatSolution_{0}_{1}.out".format(parameters["rounds"], parameters["weight"])
    os.system(order)
    order = "rm tmp_CNF_LF/UnsatSolution_{0}_{1}.out".format(parameters["rounds"], parameters["weight"])
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

    """
    stpfile.write(getStringForVariables(variables, wordsize) + '\n')
    return


def getStringForVariables(variables, wordsize):
    """

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


def GIFT128_Sbox_CNF(vary):
    """
    
    """
    command = ""
    command += "ASSERT(((~{9}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{4}) | ({9})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{8}) | ({9})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({9})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{7}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{4}) | ({6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | (~{3}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{4}) | ({7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{2}) | (~{5}) | ({9})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{5}) | ({6}) | ({9})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{2}) | ({7}) | ({9})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{3}) | ({4}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({3}) | ({4}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({2}) | ({3}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({2}) | ({5}) | ({9}) | (~{10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({3}) | ({4}) | ({7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({4}) | ({6}) | ({7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{3}) | ({5}) | ({7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({3}) | ({6}) | ({7}) | (~{10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({4}) | ({5}) | ({6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | ({4}) | (~{6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | ({4}) | (~{5}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | ({2}) | ({3}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | ({4}) | (~{5}) | (~{6}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({4}) | (~{5}) | ({6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({2}) | ({3}) | ({4}) | (~{5}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({2}) | ({3}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{2}) | ({3}) | ({4}) | ({5}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({2}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({2}) | (~{6}) | ({7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({3}) | (~{4}) | (~{6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({4}) | ({5}) | ({7}) | (~{10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{2}) | (~{6}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | (~{2}) | ({3}) | ({6})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | (~{3}) | ({4}) | (~{6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({2}) | ({6}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | ({5}) | ({6}) | ({7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | (~{2}) | ({3}) | (~{6})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | ({2}) | (~{4}) | ({5}) | (~{6})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({2}) | (~{4}) | (~{5}) | (~{6}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | (~{2}) | (~{3}) | ({5}) | (~{6}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | (~{3}) | (~{6}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({1}) | (~{4}) | (~{6}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | ({4}) | (~{6}) | (~{7}) | ({8}) | (~{9})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | (~{3}) | ({6}) | ({7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({2}) | (~{4}) | ({5}) | ({6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{2}) | (~{3}) | (~{5}) | ({6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | ({2}) | (~{3}) | ({5}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | (~{2}) | (~{4}) | (~{5}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | (~{2}) | (~{3}) | (~{5}) | (~{6})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | (~{2}) | (~{3}) | ({5}) | ({6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | ({2}) | (~{4}) | (~{5}) | ({6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({2}) | (~{3}) | (~{4}) | (~{5}) | (~{6}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{2}) | (~{3}) | (~{4}) | ({5}) | (~{6}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    return command
 

# ====== Speck cipher commands
class diff_GIFT128_CNF_Cipher:

    def createSTP(self, stp_filename, parameters):
        """
        Creates an STP file to find a characteristic for GIFT128 with
        the given parameters.
        """

        wordsize = parameters["wordsize"]
        rounds = parameters["rounds"]
        weight = parameters["weight"]
        if wordsize != 128:
            print("Only wordsize of 128-bit supported.")
            exit(1)
            
        with open(stp_filename, 'w') as stp_file:
            header = ("% Input File for STP\n% GIFT128 Wordsize={} rounds={}\n\n\n".format(wordsize, rounds))
            stp_file.write(header)

            # Setup variables
            s = ["S{}".format(i) for i in range(rounds + 1)]
            p = ["P{}".format(i) for i in range(rounds)]

            # w = weight
            w = ["w{}".format(i) for i in range(rounds)]

            setupVariables(stp_file, s, wordsize)
            setupVariables(stp_file, p, wordsize)
            setupVariables(stp_file, w, wordsize-32)
            
            setupWeightComputation(stp_file, weight, w, wordsize-32)

            for i in range(rounds):
                self.setupGIFT128Round(stp_file, s[i], p[i], s[i+1], w[i], wordsize)

            # No all zero characteristic
            assertNonZero(stp_file, s, wordsize)

            setupQuery(stp_file)

        return

    def setupGIFT128Round(self, stp_file, s_in, p, s_out, w, wordsize):
        """
        Model for differential behaviour of one round GIFT128
        """
        command = ""

        #Permutation Layer
        Per = [96,1,34,67,64,97,2,35,32,65,98,3,0,33,66,99,100,5,38,71,68,101,6,39,36,69,102,7,4,37,70,103,104,9,42,75,72,105,10,43,40,73,106,11,8,41,74,107,108,13,46,79,76,109,14,47,44,77,110,15,12,45,78,111,112,17,50,83,80,113,18,51,48,81,114,19,16,49,82,115,116,21,54,87,84,117,22,55,52,85,118,23,20,53,86,119,120,25,58,91,88,121,26,59,56,89,122,27,24,57,90,123,124,29,62,95,92,125,30,63,60,93,126,31,28,61,94,127]
        for i in range(wordsize):
            command += "ASSERT({0}[{1}:{1}] = {2}[{3}:{3}]);\n".format(p, i, s_out, Per[i])

        # Substitution Layer
        for i in range(32):
            variables = ["{0}[{1}:{1}]".format(s_in, 4*i + 3),
                         "{0}[{1}:{1}]".format(s_in, 4*i + 2),
                         "{0}[{1}:{1}]".format(s_in, 4*i + 1),
                         "{0}[{1}:{1}]".format(s_in, 4*i + 0),
                         "{0}[{1}:{1}]".format(p, 4*i + 3),
                         "{0}[{1}:{1}]".format(p, 4*i + 2),
                         "{0}[{1}:{1}]".format(p, 4*i + 1),
                         "{0}[{1}:{1}]".format(p, 4*i + 0),
                         "{0}[{1}:{1}]".format(w, 3*i + 2),
                         "{0}[{1}:{1}]".format(w, 3*i + 1),
                         "{0}[{1}:{1}]".format(w, 3*i + 0)]

            command += GIFT128_Sbox_CNF(variables)
        stp_file.write(command)
        return
#####################


def main():
    """

    """
    Initial = {"cipher" : "diff_GIFT128_CNF",
              "rounds" : 12,
              "wordsize" : 128,
              "weight" : 54,
              "endRound" : 12,
            }

    checkenviroment()
    cipher_suite = diff_GIFT128_CNF_Cipher()
    searchCharacteristics(cipher_suite, Initial)
    
if __name__ == '__main__':
    main()
    
    
