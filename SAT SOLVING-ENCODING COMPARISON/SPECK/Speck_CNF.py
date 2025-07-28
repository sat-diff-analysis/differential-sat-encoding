'''
In the name of God
'''
import os
import time
import random

wordsize=16
FullRound = 22


SearchRoundStart = 15
SearchRoundEnd = 17
InitialLowerBound = 50

#?GroupConstraintChoice = 1

# Parameters for choice 1
#?GroupNumForChoice1 = 1

DifferentialProbabilityBound = list([])
for i in range(FullRound):
    DifferentialProbabilityBound += [0]
    
def CountClausesInRoundFunction(Round, clause_num):
    count = clause_num
    # Nonzero input
    count += 1
    # Clauses for Addition
    for r in range(Round):
        for i in range(12*(wordsize-1)+4):
            count += 1
    # Clauses for xor
    for r in range(Round):
        count += 4 * wordsize
    return count
    
def CountClausesInobjectivefunction(main_var_num, cardinalitycons, clause_num):
    count = clause_num
    #number of variable used for probability: 
    n = main_var_num
    # objective function <=k
    k = cardinalitycons
    if (k > 0):
        count += 1
        for j in range(1, k):
            count += 1
        for i in range(1, n-1):
            count += 3
        for j in range(1, k):
            for i in range(1, n-1):
                count += 2
        count += 1
    if (k == 0):
        for i in range(n):
            count += 1
    return count
    
# x: list of main var (w)
# u: list of auxiliary var
# cardinalitycons=Probability: upperbound for objective function
def Genobjectivefunction(x, u, main_var_num, cardinalitycons, fout):
    n = main_var_num
    k = cardinalitycons
    if (k > 0):
        clauseseq = "-" + str(x[0]+1) + " " + str(u[0][0]+1) + " 0" + "\n"
        fout.write(clauseseq)
        for j in range(1, k):
            clauseseq = "-" + str(u[0][j]+1) + " 0" + "\n"
            fout.write(clauseseq)
        for i in range(1, n-1):
            clauseseq = "-" + str(x[i]+1) + " " + str(u[i][0]+1) + " 0" + "\n"
            fout.write(clauseseq)
            clauseseq = "-" + str(u[i-1][0]+1) + " " + str(u[i][0]+1) + " 0" + "\n"
            fout.write(clauseseq)
            clauseseq = "-" + str(x[i]+1) + " " + "-" + str(u[i-1][k-1]+1) + " 0" + "\n"
            fout.write(clauseseq)
        for j in range(1, k):
            for i in range(1, n-1):
                clauseseq = "-" + str(x[i]+1) + " " + "-" + str(u[i-1][j-1]+1) + " " + str(u[i][j]+1) + " 0" + "\n"
                fout.write(clauseseq)
                clauseseq = "-" + str(u[i-1][j]+1) + " " + str(u[i][j]+1) + " 0" + "\n"
                fout.write(clauseseq)
        clauseseq = "-" + str(x[n-1]+1) + " " + "-" + str(u[n-2][k-1]+1) + " 0" + "\n"
        fout.write(clauseseq)
    if (k == 0):
        for i in range(n):
            clauseseq = "-" + str(x[i]+1) + " 0" + "\n"
            fout.write(clauseseq)
                        
#?def Decision(Round, Probability, MatsuiRoundIndex, MatsuiCount, flag):
def Decision(Round, Probability, flag):
    #?TotalProbability = (wordsize-1)*Round
    Main_Var_Num = (wordsize-1) * Round 
    CardinalityCons = Probability

    count_var_num = 0;
    time_start = time.time()
    # Declare variable
    xin = []
    w = []
    xout = []
    for i in range(Round):
        xin.append([])
        w.append([])
        xout.append([])

        
        for j in range(wordsize*2):
            xin[i].append(0)
            xout[i].append(0)
        
        for j in range(wordsize-1):
            w[i].append(0)
            
    # Allocate variables
    for i in range(Round):
        for j in range(2*wordsize):
            xin[i][j] = count_var_num
            count_var_num += 1
        
        for j in range(wordsize-1):
            w[i][j] = count_var_num
            count_var_num += 1
        
    for i in range(Round - 1):
        for j in range(2*wordsize):
            xout[i][j] = xin[i + 1][j]
            # count_var_num += 1

    for i in range(2*wordsize):
        xout[Round - 1][i] = count_var_num
        count_var_num += 1


    auxiliary_var_u = []
    for i in range(Main_Var_Num- 1):
        auxiliary_var_u.append([])
        for j in range(Probability):
            auxiliary_var_u[i].append(count_var_num)
            count_var_num += 1
    # Count the number of clauses in the round function
    count_clause_num = 0
    count_clause_num = CountClausesInRoundFunction(Round, count_clause_num)
    # Count the number of clauses in the original sequential encoding
   
    count_clause_num = CountClausesInobjectivefunction(Main_Var_Num, CardinalityCons, count_clause_num)

    file = open("Problem-Round" + str(Round) + "-Probability" + str(Probability) + ".cnf", "w")
    file.write("p cnf " + str(count_var_num) + " " + str(count_clause_num) + "\n")
    # Add constraints to claim nonzero input difference
    clauseseq = ""
    for i in range(2*wordsize):
        clauseseq += str(xin[0][i] + 1) + " "
    clauseseq += "0" + "\n"
    file.write(clauseseq)
    # Add constraints for the round function
    for r in range(Round):
        
 
        SymbolicCNFConstraintForAddition = [[1, 1, 1, 9, 9, 9, 1], [0, 0, 0, 9, 9, 9, 1], [0, 1, 9, 9, 9, 9, 0], [1, 9, 0, 9, 9, 9, 0], 
        [9, 0, 9, 1, 1, 1, 0], [9, 9, 1, 0, 1, 1, 0], [9, 9, 1, 1, 0, 1, 0],[9, 0, 9, 0, 0, 1, 0],[9, 9, 1, 1, 1, 0, 0],[9, 0, 9, 0, 1, 0, 0],
        [9, 0, 9, 1, 0, 0, 0],[9, 9, 1, 0, 0, 0, 0]]

        xin[r].reverse()
        xout[r].reverse()
        w[r].reverse()
        
        #----Rotations in inputs 
        #--a_in >>> 7        
        InputA_Rotate = list([])
        for i in range(7):
            InputA_Rotate += [xin[r][(wordsize*0) + i + (wordsize-7)]] 
        for i in range(7,wordsize):
            InputA_Rotate += [xin[r][(wordsize*0) + i - 7]]
        #--b_in <<< 2
        inputB_Rotate = list([])
        for i in range(wordsize-2):
            inputB_Rotate += [xin[r][(wordsize*1) + i + 2]] 
        for i in range(wordsize-2,wordsize):
            inputB_Rotate += [xin[r][(wordsize*1) + i - (wordsize-2)]]
        
        #----Constraints for first addition
        #--first condition
        #-tow XOR
        # a = InputA_Rotate[0]
        # b = xin[r][wordsize]
        # c = xout[r][0]

        a = InputA_Rotate[16-1]
        b = xin[r][2*16 - 1]
        c = xout[r][16-1]

        clauseseq = str(a + 1) + " " + str(b + 1) + " " + "-" + str(c + 1) + " " + "0" + "\n"
        file.write(clauseseq)
        clauseseq = str(a + 1) + " " + "-" + str(b + 1) + " " + str(c + 1) + " " + "0" + "\n"
        file.write(clauseseq)
        clauseseq = "-" + str(a + 1) + " " + str(b + 1) + " " + str(c + 1) + " " + "0" + "\n"
        file.write(clauseseq)
        clauseseq = "-" + str(a + 1) + " " + "-" + str(b + 1) + " " + "-" + str(c + 1) + " " + "0" + "\n"
        file.write(clauseseq)
        #--second condition
        for i in range(wordsize-1, 0, -1):
            for j in range(12):
                X = list([])
                X += [InputA_Rotate[i]]
                X += [xin[r][wordsize + i]]
                X += [xout[r][i]]
                X += [InputA_Rotate[i - 1]]
                X += [xin[r][wordsize + i - 1]]
                X += [xout[r][i - 1]]
                X +=[w[r][i - 1]]
                clauseseq = ""
                for k in range(7):
                    if (SymbolicCNFConstraintForAddition[j][k] == 1):
                        clauseseq += "-" + str(X[k] + 1) + " "
                    if (SymbolicCNFConstraintForAddition[j][k] == 0):
                        clauseseq += str(X[k] + 1) + " "
                clauseseq += "0" + "\n"
                file.write(clauseseq) 

        #----Constraints for  XOR
        #--tow XOR
        for i in range(wordsize-1, -1, -1):
            a = xout[r][i]
            b = inputB_Rotate[i]
            c = xout[r][wordsize+i]
            clauseseq = str(a + 1) + " " + str(b + 1) + " " + "-" + str(c + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            clauseseq = str(a + 1) + " " + "-" + str(b + 1) + " " + str(c + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            clauseseq = "-" + str(a + 1) + " " + str(b + 1) + " " + str(c + 1) + " " + "0" + "\n"
            file.write(clauseseq)
            clauseseq = "-" + str(a + 1) + " " + "-" + str(b + 1) + " " + "-" + str(c + 1) + " " + "0" + "\n"
            file.write(clauseseq)
    # Add constraints for the original sequential encoding

    Main_Vars = list([])
    for r in range(Round):
        # for i in range(wordsize-1):
        for i in range(wordsize-2, -1, -1):    
            Main_Vars += [w[Round - 1 - r][i]]
            
            
           
    Genobjectivefunction(Main_Vars, auxiliary_var_u, Main_Var_Num, CardinalityCons, file)
    file.close()
    # Call solver cadical
    #/home/user/program/lingeling/treengeling

    order = "/home/user/cadical-master/build/cadical " + "Problem-Round" + str(Round) + "-Probability" + str(Probability) + ".cnf > Round" + str(Round) + "-Probability" + str(Probability) + "-solution.out"
    os.system(order)
    # Extracting results
    order = "sed -n '/s SATISFIABLE/p' Round" + str(Round) + "-Probability" + str(Probability) + "-solution.out > SatSolution.out"
    os.system(order)
    order = "sed -n '/s UNSATISFIABLE/p' Round" + str(Round) + "-Probability" + str(Probability) + "-solution.out > UnsatSolution.out"
    os.system(order)
    satsol = open("SatSolution.out")
    unsatsol = open("UnsatSolution.out")
    satresult = satsol.readlines()
    unsatresult = unsatsol.readlines()
    satsol.close()
    unsatsol.close()
    if ((len(satresult) == 0) and (len(unsatresult) > 0)):
        flag = False
    if ((len(satresult) > 0) and (len(unsatresult) == 0)):
        flag = True
    order = "rm SatSolution.out"
    os.system(order)
    order = "rm UnsatSolution.out"
    os.system(order)
    # Removing cnf file
    #order = "rm Problem-Round" + str(Round) + "-Probability" + str(Probability) + ".cnf"
    #os.system(order)
    time_end = time.time()
    # Printing solutions
    if (flag == True):
        print("Round:" + str(Round) + "; Probability: " + str(Probability) + "; Sat; TotalCost: " + str(time_end - time_start))
    else:
        print("Round:" + str(Round) + "; Probability: " + str(Probability) + "; Unsat; TotalCost: " + str(time_end - time_start))
    return flag
            
# main function
CountProbability = InitialLowerBound
TotalTimeStart = time.time()
for totalround in range(SearchRoundStart, SearchRoundEnd):
    flag = False
    time_start = time.time()

    while (flag == False):
        #?flag = Decision(totalround, CountProbability, MatsuiRoundIndex, MatsuiCount, flag)
        flag = Decision(totalround, CountProbability, flag)
        CountProbability += 1
    DifferentialProbabilityBound[totalround] = CountProbability - 1
    time_end = time.time()
    file = open("RunTimeSummarise.out", "a")
    resultseq = "Round: " + str(totalround) + "; Differential Probability: " + str(DifferentialProbabilityBound[totalround]) + "; Runtime: " + str(time_end - time_start) + "\n"
    file.write(resultseq)
    file.close()
print(str(DifferentialProbabilityBound))
TotalTimeEnd = time.time()
print("Total Runtime: " + str(TotalTimeEnd - TotalTimeStart))
file = open("RunTimeSummarise.out", "a")
resultseq = "Total Runtime: " + str(TotalTimeEnd - TotalTimeStart)
file.write(resultseq)











