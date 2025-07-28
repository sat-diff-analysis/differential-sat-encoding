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

    if not os.path.exists("./tmp_CVC_pure/"):
        os.makedirs("./tmp_CVC_pure/")

    return
# ======= 
def findMinWeightCharacteristic(cipher, parameters):
    """
    Find a characteristic of minimal weight for the cipher
    parameters = [rounds, wordsize, weight, isIterative, fixedVariables]
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
    Searches for differential characteristics of minimal weight for an increasing number of rounds.
    """
    ##########
    Destance = "tmp_CVC_pure/{}_Speed Test.txt".format(parameters["cipher"])
    d = ""   
    ##########
    HW_rnd = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
    # parameters["Pr_Round"] = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
    parameters["time"] = 0
    e = 0
    while not parameters["endRound"] == (parameters["rounds"] - 1):

        parameters["weight"] = findMinWeightCharacteristic(cipher, parameters)
        d += "Characteristic for Rounds {} Weight {} - Time {}s\n".format(parameters["rounds"], parameters["weight"], parameters["time"])
        with open(Destance, "w") as dec:
            dec.write(d)
        parameters["rounds"] = parameters["rounds"] + 1
        #########11
        HW_rnd[e] = parameters["weight"]
        # parameters["Pr_Round"].append(parameters["weight"])
        if (parameters["rounds"] > 2):
            for r in range((int(parameters["rounds"]/2)) - 1):
                if ((HW_rnd[r] + HW_rnd[parameters["rounds"] - 2 - r]) > parameters["weight"]):
                    parameters["weight"] = (HW_rnd[r] + HW_rnd[parameters["rounds"] - 2 - r])
        e = e + 1
        # print(parameters["Pr_Round"])
    print(HW_rnd)
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

def diff_Add_CVC(self,a, b, c, w, wordsize):

    command = "ASSERT("
    command += "(((BVXOR((~{0} << 1)[{3}:0], ({1} << 1)[{3}:0])".format(
        a, b, c, wordsize - 1)
    command += "& BVXOR((~{0} << 1)[{3}:0], ({2} << 1)[{3}:0]))".format(
        a, b, c, wordsize - 1)
    command += " & BVXOR({0}, BVXOR({1}, BVXOR({2}, ({1} << 1)[{3}:0]))))".format(
        a, b, c, wordsize - 1)
    command += " = 0bin{})".format("0" * wordsize)
    command += ");\n"
    # getStringEq(a, b, c)
    command += "ASSERT({0} = ~".format(w)
    command += "(BVXOR(~{0}, {1}) & BVXOR(~{0}, {2}))".format(a, b, c)
    command += ");\n"
    return command
 
def diff_Xor_CVC(self,a, b, c, wordsize):
    
    command = "ASSERT(" + a + " = "
    command += "BVXOR(" + b + ","
    command += c
    command += "));\n"
    return command
# ====== Speck cipher commands
class Diff_Speck_CVC_Cipher:


    def createSTP(self, stp_filename, parameters):
        """
        Creates an STP file to find a characteristic for SPECK with
        the given parameters.
        """
        wordsize = parameters["wordsize"]
        blocksize = parameters["blocksize"]
        rounds = parameters["rounds"]
        weight = parameters["weight"]
        #self.language = "CNF"

        #------
        if wordsize == 16:
            self.rot_alpha = 7
            self.rot_beta = 2
        else:
            self.rot_alpha = 8
            self.rot_beta = 3

        with open(stp_filename, 'w') as stp_file:
            stp_file.write("% Input File for STP\n% Speck w={} alpha={} beta={} rounds={}\n\n\n".format(wordsize, self.rot_alpha, self.rot_beta, rounds))

            x = ["x{}".format(i) for i in range(rounds + 1)]
            y = ["y{}".format(i) for i in range(rounds + 1)]
            w = ["w{}".format(i) for i in range(rounds)]

            setupVariables(stp_file, x, wordsize)
            setupVariables(stp_file, y, wordsize)
            setupVariables(stp_file, w, wordsize)

            # Ignore MSB
            setupWeightComputation(stp_file, weight, w, wordsize, 1)
            
            for i in range(rounds):
                self.setupSpeckRound(stp_file, x[i], y[i], x[i+1], y[i+1], w[i], wordsize)

            # No all zero characteristic
            assertNonZero(stp_file, x + y, wordsize)

            setupQuery(stp_file)

        return

    def setupSpeckRound(self, stp_file, x_in, y_in, x_out, y_out, w, wordsize):
        """
        Model for differential behaviour of one round SPECK
        """
        command = ""

        command += diff_Add_CVC(self,rotr(x_in, self.rot_alpha, wordsize), y_in, x_out, w,wordsize)

        command += diff_Xor_CVC(self,rotl(y_in, self.rot_beta, wordsize),x_out,y_out, wordsize)
             
        stp_file.write(command)
        return
#####################


def main():
    """
    Parse the arguments and start the request functionality with the provided
    parameters.
    """
    Initial = {"cipher" : "diff_speck_CVC",
              "rounds" : 17,
              "wordsize" : 16,
              "blocksize" : 32,
              "weight" : 58,
              "endRound" : 17,
            }

    checkenviroment()
    cipher_suite = Diff_Speck_CVC_Cipher()

    # Initial["cipher"] = cipher_suite

    searchCharacteristics(cipher_suite, Initial)
    
if __name__ == '__main__':
    main()
    
