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

def LBlock_Sbox0_CNF(vary):
    """
    
    """
    command = ""
    command += "ASSERT(((~{2}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{3}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{5}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{8}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({9}) | (~{10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{6}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | ({5}) | ({6})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({4}) | ({6}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({3}) | (~{6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({3}) | (~{4}) | ({7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{3}) | ({4}) | ({7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({4}) | (~{5}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | ({2}) | ({3}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | (~{2}) | (~{3}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | ({6}) | ({7}) | (~{9})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{4}) | (~{5}) | ({6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({1}) | (~{2}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({1}) | (~{3}) | (~{6}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({2}) | ({4}) | ({5}) | ({6})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{4}) | ({5}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({2}) | (~{3}) | (~{6}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | (~{2}) | (~{3}) | ({5}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | ({3}) | (~{4}) | (~{6}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({2}) | (~{3}) | (~{5}) | (~{6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({2}) | ({4}) | ({5}) | (~{6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | ({2}) | (~{3}) | ({5}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | (~{2}) | ({3}) | ({5}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({2}) | ({3}) | (~{5}) | (~{6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{2}) | (~{3}) | (~{5}) | (~{6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({2}) | (~{4}) | (~{5}) | ({6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{2}) | ({4}) | ({5}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{2}) | (~{4}) | (~{5}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | (~{2}) | ({4}) | (~{5}) | (~{6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({2}) | ({4}) | (~{5}) | (~{6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({2}) | (~{4}) | ({5}) | (~{6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    return command

def LBlock_Sbox1_6_7_CNF(vary):
    """
    
    """
    command = ""
    command += "ASSERT(((~{2}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{3}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{5}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{8}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({9}) | (~{10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{6}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | ({5}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({3}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({4}) | ({6}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({3}) | (~{4}) | ({6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{3}) | ({4}) | ({6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({4}) | (~{5}) | (~{6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | ({2}) | ({3}) | (~{6})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | (~{2}) | (~{3}) | (~{6})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | ({6}) | ({7}) | (~{9})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{4}) | (~{5}) | ({7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({1}) | (~{2}) | (~{6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({1}) | (~{3}) | ({6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({2}) | ({4}) | ({5}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{4}) | ({5}) | (~{6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({2}) | (~{3}) | ({6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | (~{2}) | (~{3}) | ({5}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | ({3}) | (~{4}) | ({6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({2}) | (~{3}) | (~{5}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({2}) | ({4}) | ({5}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | ({2}) | (~{3}) | ({5}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | (~{2}) | ({3}) | ({5}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({2}) | ({3}) | (~{5}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{2}) | (~{3}) | (~{5}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({2}) | (~{4}) | (~{5}) | (~{6}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{2}) | ({4}) | ({5}) | (~{6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{2}) | (~{4}) | (~{5}) | (~{6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | (~{2}) | ({4}) | (~{5}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({2}) | ({4}) | (~{5}) | (~{6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({2}) | (~{4}) | ({5}) | (~{6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    return command

def LBlock_Sbox2_CNF(vary):
    """

    """
    command = ""
    command += "ASSERT(((~{2}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{3}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{7}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{8}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({9}) | (~{10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({4}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{4}) | (~{6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | ({4}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({4}) | ({5}) | ({6})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({3}) | (~{4}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({3}) | (~{5}) | ({6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{3}) | ({5}) | ({6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({5}) | (~{6}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | ({2}) | ({3}) | (~{6})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | (~{2}) | (~{3}) | (~{6})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | ({4}) | ({6}) | (~{9})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({4}) | (~{5}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({1}) | (~{2}) | (~{6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({1}) | (~{3}) | (~{4}) | ({6})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({2}) | ({4}) | ({5}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{5}) | (~{6}) | ({7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({2}) | (~{3}) | (~{4}) | ({6})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | (~{2}) | (~{3}) | ({7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | ({3}) | (~{4}) | (~{5}) | ({6})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({2}) | (~{3}) | (~{4}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({2}) | (~{4}) | ({5}) | ({7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | ({2}) | (~{3}) | ({7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | (~{2}) | ({3}) | ({7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({2}) | ({3}) | (~{4}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{2}) | (~{3}) | (~{4}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({2}) | ({4}) | (~{5}) | (~{6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{2}) | ({5}) | (~{6}) | ({7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{2}) | (~{5}) | (~{6}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | (~{2}) | (~{4}) | ({5}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({2}) | (~{4}) | ({5}) | (~{6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({2}) | (~{4}) | (~{5}) | (~{6}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    return command   

def LBlock_Sbox3_CNF(vary):
    """
    
    """
    command = ""
    command += "ASSERT(((~{2}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{3}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{4}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{8}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({9}) | (~{10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({5}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{5}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | ({4}) | ({5})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({2}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({5}) | ({6}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({3}) | (~{5}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({3}) | (~{6}) | ({7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{3}) | ({6}) | ({7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({4}) | ({5}) | ({6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{4}) | ({6}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | ({2}) | ({3}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | ({2}) | ({7}) | (~{10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | (~{2}) | (~{3}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | ({5}) | ({7}) | (~{9})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{4}) | ({5}) | (~{6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({1}) | (~{2}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({1}) | (~{3}) | (~{5}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({4}) | (~{6}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | ({2}) | ({4}) | ({6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | (~{2}) | (~{3}) | ({4}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | ({3}) | (~{5}) | (~{6}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({2}) | (~{3}) | (~{4}) | (~{5}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | ({2}) | (~{3}) | ({4}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | (~{2}) | ({3}) | ({4}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({2}) | ({3}) | (~{4}) | (~{5}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{2}) | (~{3}) | (~{4}) | (~{5}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{2}) | ({4}) | ({6}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{2}) | (~{4}) | (~{6}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{4}) | ({5}) | (~{6}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | (~{2}) | (~{4}) | (~{5}) | ({6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({2}) | (~{4}) | (~{5}) | ({6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({2}) | ({4}) | (~{5}) | (~{6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    return command  

def LBlock_Sbox4_CNF(vary):
    """
    
    """
    command = ""
    command += "ASSERT(((~{2}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{3}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{6}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{8}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({9}) | (~{10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({4}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{4}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | ({4}) | ({6})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({4}) | ({5}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({3}) | (~{4}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({3}) | (~{5}) | ({7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{3}) | ({5}) | ({7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({5}) | (~{6}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | ({2}) | ({3}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | (~{2}) | (~{3}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | ({4}) | ({7}) | (~{9})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({4}) | (~{5}) | (~{6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({2}) | ({4}) | ({5}) | ({6})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{5}) | ({6}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({1}) | (~{2}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({1}) | (~{3}) | (~{4}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({2}) | (~{3}) | (~{4}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | (~{2}) | (~{3}) | ({6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | ({3}) | (~{4}) | (~{5}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({2}) | (~{3}) | (~{4}) | (~{6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({2}) | (~{4}) | ({5}) | ({6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | ({2}) | (~{3}) | ({6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | (~{2}) | ({3}) | ({6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({2}) | ({3}) | (~{4}) | (~{6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{2}) | (~{3}) | (~{4}) | (~{6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({2}) | ({4}) | (~{5}) | (~{6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{2}) | ({5}) | ({6}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{2}) | (~{5}) | (~{6}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | (~{2}) | (~{4}) | ({5}) | (~{6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({2}) | (~{4}) | ({5}) | (~{6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({2}) | (~{4}) | (~{5}) | ({6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    return command  

def LBlock_Sbox5_CNF(vary):
    """
    
    """
    command = ""
    command += "ASSERT(((~{2}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{3}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{6}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{8}) | ({10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({9}) | (~{10})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({5}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{5}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | ({5}) | ({6})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({4}) | ({5}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({3}) | (~{5}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({3}) | (~{4}) | ({7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{3}) | ({4}) | ({7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({4}) | (~{6}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | ({2}) | ({3}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | (~{2}) | (~{3}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({1}) | ({5}) | ({7}) | (~{9})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{4}) | ({5}) | (~{6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({1}) | (~{2}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({1}) | (~{3}) | (~{5}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({2}) | ({4}) | ({5}) | ({6})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{4}) | ({6}) | (~{7}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({1}) | ({2}) | (~{3}) | (~{5}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | (~{2}) | (~{3}) | ({6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | ({3}) | (~{4}) | (~{5}) | ({7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({2}) | (~{3}) | (~{5}) | (~{6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({2}) | ({4}) | (~{5}) | ({6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | ({2}) | (~{3}) | ({6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{1}) | (~{2}) | ({3}) | ({6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | ({2}) | ({3}) | (~{5}) | (~{6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT((({0}) | (~{2}) | (~{3}) | (~{5}) | (~{6}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | ({2}) | (~{4}) | ({5}) | (~{6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{2}) | ({4}) | ({6}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{2}) | (~{4}) | (~{6}) | (~{7}) | (~{8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{1}) | (~{2}) | ({4}) | (~{5}) | (~{6}) | ({8})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({2}) | ({4}) | (~{5}) | (~{6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    command += "ASSERT(((~{0}) | (~{1}) | ({2}) | (~{4}) | (~{5}) | ({6}) | (~{7})) = 0bin1);\n".format(vary[0], vary[1], vary[2], vary[3], vary[4], vary[5], vary[6], vary[7], vary[8], vary[9], vary[10])
    return command  

def diff_Xor_CNF(a, b, c, wordsize):

    command = ""
    for i in range(wordsize):
        command += "ASSERT((({0}[{3}:{3}]) | ({1}[{3}:{3}]) | (~{2}[{3}:{3}])) = 0bin1);\n".format(a, b, c, i)
        command += "ASSERT((({0}[{3}:{3}]) | (~{1}[{3}:{3}]) | ({2}[{3}:{3}])) = 0bin1);\n".format(a, b, c, i)
        command += "ASSERT(((~{0}[{3}:{3}]) | ({1}[{3}:{3}]) | ({2}[{3}:{3}])) = 0bin1);\n".format(a, b, c, i)
        command += "ASSERT(((~{0}[{3}:{3}]) | (~{1}[{3}:{3}]) | (~{2}[{3}:{3}])) = 0bin1);\n".format(a, b, c, i)
    return command

# ====== LBlock cipher commands
class Diff_LBlock_CNF_Cipher:

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
            setupVariables(stp_file, w, wordsize-8)

            setupWeightComputation(stp_file, weight, w, wordsize-8)

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
        command += diff_Xor_CNF(f_out, y_in_rot, x_out, wordsize)

        stp_file.write(command)
        return
    
    def F(self, f_in, s_out, f_out, w):
        """
        Model for the F function used in LBlock
        """
        command = ""

        # Substitution Layer

        #s0
        variables = ["{0}[{1}:{1}]".format(f_in, 3),
                     "{0}[{1}:{1}]".format(f_in, 2),
                     "{0}[{1}:{1}]".format(f_in, 1),
                     "{0}[{1}:{1}]".format(f_in, 0),
                     "{0}[{1}:{1}]".format(s_out, 3),
                     "{0}[{1}:{1}]".format(s_out, 2),
                     "{0}[{1}:{1}]".format(s_out, 1),
                     "{0}[{1}:{1}]".format(s_out, 0),
                     "{0}[{1}:{1}]".format(w, 2),
                     "{0}[{1}:{1}]".format(w, 1),
                     "{0}[{1}:{1}]".format(w, 0)]
        command += LBlock_Sbox0_CNF(variables)

        #s1
        variables = ["{0}[{1}:{1}]".format(f_in, 7),
                     "{0}[{1}:{1}]".format(f_in, 6),
                     "{0}[{1}:{1}]".format(f_in, 5),
                     "{0}[{1}:{1}]".format(f_in, 4),
                     "{0}[{1}:{1}]".format(s_out, 7),
                     "{0}[{1}:{1}]".format(s_out, 6),
                     "{0}[{1}:{1}]".format(s_out, 5),
                     "{0}[{1}:{1}]".format(s_out, 4),
                     "{0}[{1}:{1}]".format(w, 5),
                     "{0}[{1}:{1}]".format(w, 4),
                     "{0}[{1}:{1}]".format(w, 3)]
        command += LBlock_Sbox1_6_7_CNF(variables)

        #s2
        variables = ["{0}[{1}:{1}]".format(f_in, 11),
                     "{0}[{1}:{1}]".format(f_in, 10),
                     "{0}[{1}:{1}]".format(f_in, 9),
                     "{0}[{1}:{1}]".format(f_in, 8),
                     "{0}[{1}:{1}]".format(s_out, 11),
                     "{0}[{1}:{1}]".format(s_out, 10),
                     "{0}[{1}:{1}]".format(s_out, 9),
                     "{0}[{1}:{1}]".format(s_out, 8),
                     "{0}[{1}:{1}]".format(w, 8),
                     "{0}[{1}:{1}]".format(w, 7),
                     "{0}[{1}:{1}]".format(w, 6)]
        command += LBlock_Sbox2_CNF(variables)

        #s3
        variables = ["{0}[{1}:{1}]".format(f_in, 15),
                     "{0}[{1}:{1}]".format(f_in, 14),
                     "{0}[{1}:{1}]".format(f_in, 13),
                     "{0}[{1}:{1}]".format(f_in, 12),
                     "{0}[{1}:{1}]".format(s_out, 15),
                     "{0}[{1}:{1}]".format(s_out, 14),
                     "{0}[{1}:{1}]".format(s_out, 13),
                     "{0}[{1}:{1}]".format(s_out, 12),
                     "{0}[{1}:{1}]".format(w, 11),
                     "{0}[{1}:{1}]".format(w, 10),
                     "{0}[{1}:{1}]".format(w, 9)]
        command += LBlock_Sbox3_CNF(variables)

        #s4
        variables = ["{0}[{1}:{1}]".format(f_in, 19),
                     "{0}[{1}:{1}]".format(f_in, 18),
                     "{0}[{1}:{1}]".format(f_in, 17),
                     "{0}[{1}:{1}]".format(f_in, 16),
                     "{0}[{1}:{1}]".format(s_out, 19),
                     "{0}[{1}:{1}]".format(s_out, 18),
                     "{0}[{1}:{1}]".format(s_out, 17),
                     "{0}[{1}:{1}]".format(s_out, 16),
                     "{0}[{1}:{1}]".format(w, 14),
                     "{0}[{1}:{1}]".format(w, 13),
                     "{0}[{1}:{1}]".format(w, 12)]
        command += LBlock_Sbox4_CNF(variables)

        #s5
        variables = ["{0}[{1}:{1}]".format(f_in, 23),
                     "{0}[{1}:{1}]".format(f_in, 22),
                     "{0}[{1}:{1}]".format(f_in, 21),
                     "{0}[{1}:{1}]".format(f_in, 20),
                     "{0}[{1}:{1}]".format(s_out, 23),
                     "{0}[{1}:{1}]".format(s_out, 22),
                     "{0}[{1}:{1}]".format(s_out, 21),
                     "{0}[{1}:{1}]".format(s_out, 20),
                     "{0}[{1}:{1}]".format(w, 17),
                     "{0}[{1}:{1}]".format(w, 16),
                     "{0}[{1}:{1}]".format(w, 15)]
        command += LBlock_Sbox5_CNF(variables)

        #s6
        variables = ["{0}[{1}:{1}]".format(f_in, 27),
                     "{0}[{1}:{1}]".format(f_in, 26),
                     "{0}[{1}:{1}]".format(f_in, 25),
                     "{0}[{1}:{1}]".format(f_in, 24),
                     "{0}[{1}:{1}]".format(s_out, 27),
                     "{0}[{1}:{1}]".format(s_out, 26),
                     "{0}[{1}:{1}]".format(s_out, 25),
                     "{0}[{1}:{1}]".format(s_out, 24),
                     "{0}[{1}:{1}]".format(w, 20),
                     "{0}[{1}:{1}]".format(w, 19),
                     "{0}[{1}:{1}]".format(w, 18)]
        command += LBlock_Sbox1_6_7_CNF(variables)

        #s7
        variables = ["{0}[{1}:{1}]".format(f_in, 31),
                     "{0}[{1}:{1}]".format(f_in, 30),
                     "{0}[{1}:{1}]".format(f_in, 29),
                     "{0}[{1}:{1}]".format(f_in, 28),
                     "{0}[{1}:{1}]".format(s_out, 31),
                     "{0}[{1}:{1}]".format(s_out, 30),
                     "{0}[{1}:{1}]".format(s_out, 29),
                     "{0}[{1}:{1}]".format(s_out, 28),
                     "{0}[{1}:{1}]".format(w, 23),
                     "{0}[{1}:{1}]".format(w, 22),
                     "{0}[{1}:{1}]".format(w, 21)]
        command += LBlock_Sbox1_6_7_CNF(variables)

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

    """
    Initial = {"cipher" : "diff_LBlock_CNF",
              "rounds" : 29,
              "wordsize" : 32,
              "weight" : 131,
              "endRound" : 33,
            }

    checkenviroment()
    cipher_suite = Diff_LBlock_CNF_Cipher()
    searchCharacteristics(cipher_suite, Initial)
    
if __name__ == '__main__':
    main()
    
    
