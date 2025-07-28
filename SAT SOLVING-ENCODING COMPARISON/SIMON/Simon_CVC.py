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

def diff_And_SimonLike_CVC(x_in,x_in_rotalpha,x_in_rotbeta, and_out, w, wordsize, parameters):
    command = ""

    #Deal with dependent inputs
    varibits = "({0} | {1})".format(x_in_rotalpha, x_in_rotbeta)
    doublebits = getDoubleBits(x_in, wordsize, parameters)

    #Check for valid difference
    firstcheck = "({} & ~{})".format(and_out, varibits)
    secondcheck = "(BVXOR({}, {}) & {})".format(and_out, rotl(and_out, parameters["rot_alpha"] - parameters["rot_beta"], wordsize), doublebits)
    thirdcheck = "(IF {0} = 0x{1} THEN BVMOD({2}, {3}, 0x{4}2) ELSE 0x{5} ENDIF)".format(x_in, "f" * (wordsize // 4), wordsize, and_out, "0" * (wordsize // 4 - 1),
        "0" * (wordsize // 4))

    command += "ASSERT(({} | {} | {}) = 0x{});\n".format(
        firstcheck, secondcheck, thirdcheck, "0" * (wordsize // 4))

    #Weight computation
    command += "ASSERT({0} = (IF {1} = 0x{4} THEN BVSUB({5},0x{4},0x{6}1) \
                ELSE BVXOR({2}, {3}) ENDIF));\n".format(
                    w, x_in, varibits, doublebits, "f" * (wordsize // 4),
                    wordsize, "0"*((wordsize // 4) - 1))

    return command

def getDoubleBits(x_in, wordsize, parameters):
        command = "({0} & ~{1} & {2})".format(
        rotl(x_in, parameters["rot_beta"], wordsize),
        rotl(x_in, parameters["rot_alpha"], wordsize),
        rotl(x_in, 2 * parameters["rot_alpha"] - parameters["rot_alpha"], wordsize))
        return command


# ====== Simon cipher commands
class Diff_Simon_CVC_Cipher:

    def createSTP(self, stp_filename, parameters):
        """
        Creates an STP file to find a characteristic for Simon with
        the given parameters.
        """

        wordsize = parameters["wordsize"]
        blocksize = parameters["blocksize"]
        rounds = parameters["rounds"]
        weight = parameters["weight"]

        with open(stp_filename, 'w') as stp_file:
            stp_file.write("% Input File for STP\n% Simon w={} alpha={} beta={}"
                      " gamma={} rounds={}\n\n\n".format(wordsize, parameters["rot_alpha"], parameters["rot_beta"], parameters["rot_gamma"], rounds))
	        # Setup variables
            # x = left, y = right
            x = ["x{}".format(i) for i in range(rounds + 1)]
            y = ["y{}".format(i) for i in range(rounds + 1)]
            and_out = ["andout{}".format(i) for i in range(rounds)]
            # w = weight
            w = ["w{}".format(i) for i in range(rounds)]                                          
                                                    

            setupVariables(stp_file, x, wordsize)
            setupVariables(stp_file, y, wordsize)
            setupVariables(stp_file, and_out, wordsize)
            setupVariables(stp_file, w, wordsize)

            # Ignore MSB
            setupWeightComputation(stp_file, weight, w, wordsize)
            
            for i in range(rounds):
                self.setupSimonRound(stp_file, x[i], y[i], x[i+1], y[i+1],
                                     and_out[i], w[i], wordsize, parameters)

            # No all zero characteristic
            assertNonZero(stp_file, x + y, wordsize)

            setupQuery(stp_file)
         
        return

    def setupSimonRound(self, stp_file, x_in, y_in, x_out, y_out,and_out, w, wordsize, parameters):
        """

        """
        command = ""


        #--Assert(y_out = x_in)
        command += "ASSERT({} = {});\n".format(y_out, x_in)

        #--x_in <<< rot_alpha 
        x_in_rotalpha = rotl(x_in,  parameters["rot_alpha"], wordsize)
        #--x_in <<< rot_beta 
        x_in_rotbeta = rotl(x_in, parameters["rot_beta"], wordsize)
        #--x_in <<< rot_beta 
        x_in_rotgamma = rotl(x_in, parameters["rot_gamma"], wordsize)
    
        #--Assert dependent and -->  (x_in <<< rot_alpha) And (x_in <<< rot_beta) = and_out
        command += diff_And_SimonLike_CVC(x_in, x_in_rotalpha, x_in_rotbeta, and_out, w, wordsize, parameters)

        #--Assert 2 XORs -->  (and_out) Xor (y_in) Xor (x_in <<< rot_gamma) = x_out
        command += "ASSERT({} = BVXOR({}, BVXOR({}, {})));\n".format( x_out, x_in_rotgamma, y_in, and_out)

        stp_file.write(command)
        return

#####################


def main():
    """
    Parse the arguments and start the request functionality with the provided
    parameters.
    """
    Initial = {"cipher" : "diff_Simon_CVC",
              "rounds" : 1,
              "wordsize" : 16,
              "blocksize" : 32,
              "weight" : 0,
              "endRound" : 32,
              "rot_alpha" : 8,
              "rot_beta" : 1,
              "rot_gamma" : 2,
            }

    checkenviroment()
    cipher_suite = Diff_Simon_CVC_Cipher()

    searchCharacteristics(cipher_suite, Initial)
    
if __name__ == '__main__':
    main()
    
