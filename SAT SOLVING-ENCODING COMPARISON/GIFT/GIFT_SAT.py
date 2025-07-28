'''
In the name of God
'''
import os
import time
import random


FullRound =40
SearchRoundStart = 14
SearchRoundEnd =15
InitialLowerBound = 67

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
    # Clauses for Sbox
    for r in range(Round):
        for i in range(32):
            for j in range(54):
                count += 1
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
    
    Main_Var_Num = 32 * Round * 3
    CardinalityCons = Probability

    count_var_num = 0;
    time_start = time.time()
    # Declare variable
    xin = []
    p = []
    q = []
    m = []
    xout = []
    for i in range(Round):
        xin.append([])
        p.append([])
        q.append([])
        m.append([])
        xout.append([])
        for j in range(128):
            xin[i].append(0)
        for j in range(32):
            p[i].append(0)
            q[i].append(0)
            m[i].append(0)
        for j in range(128):
            xout[i].append(0)
    # Allocate variables
    for i in range(Round):
        for j in range(128):
            xin[i][j] = count_var_num
            count_var_num += 1
        for j in range(32):
            p[i][j] = count_var_num
            count_var_num += 1
        for j in range(32):
            q[i][j] = count_var_num
            count_var_num += 1
        for j in range(32):
            m[i][j] = count_var_num
            count_var_num += 1
    for i in range(Round - 1):
        for j in range(128):
            xout[i][j] = xin[i + 1][j]
    for i in range(128):
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

    
    file = open("Present-Round" + str(Round) + "-Probability" + str(Probability) + ".cnf", "w")
    file.write("p cnf " + str(count_var_num) + " " + str(count_clause_num) + "\n")
    # Add constraints to claim nonzero input difference
    clauseseq = ""
    for i in range(128):
        clauseseq += str(xin[0][i] + 1) + " "
    clauseseq += "0" + "\n"
    file.write(clauseseq)
    
    # Add constraints for the round function
    for r in range(Round):
        y = list([])
        P = [96,1,34,67,64,97,2,35,32,65,98,3,0,33,66,99,100,5,38,71,68,101,6,39,36,69,102,7,4,37,70,103,104,9,42,75,72,105,10,43,40,73,106,11,8,41,74,107,108,13,46,79,76,109,14,47,44,77,110,15,12,45,78,111,112,17,50,83,80,113,18,51,48,81,114,19,16,49,82,115,116,21,54,87,84,117,22,55,52,85,118,23,20,53,86,119,120,25,58,91,88,121,26,59,56,89,122,27,24,57,90,123,124,29,62,95,92,125,30,63,60,93,126,31,28,61,94,127]
        SymbolicCNFConstraintForSbox = [ # Differential Probability GIFT (54)
            [1, 1, 1, 0, 9, 9, 1, 9, 9, 9, 9],
            [0, 1, 0, 9, 1, 0, 1, 9, 9, 9, 9],
            [0, 0, 0, 9, 1, 1, 0, 1, 9, 9, 9],
            [9, 0, 0, 9, 1, 1, 1, 0, 9, 9, 9],
            [0, 0, 1, 1, 9, 0, 0, 1, 9, 9, 9],
            [9, 0, 1, 1, 9, 0, 1, 0, 9, 9, 9],
            [0, 1, 1, 1, 9, 1, 1, 9, 9, 9, 9],
            [9, 9, 9, 9, 9, 9, 9, 9, 9, 1, 0],
            [9, 9, 9, 9, 1, 9, 9, 9, 9, 0, 9],
            [9, 9, 9, 9, 9, 9, 9, 9, 1, 0, 9],
            [9, 9, 9, 1, 0, 9, 9, 1, 0, 9, 9],
            [9, 9, 9, 9, 1, 9, 0, 9, 0, 9, 9],
            [9, 0, 9, 1, 9, 9, 9, 9, 0, 9, 9],
            [9, 0, 9, 0, 9, 9, 0, 0, 9, 9, 1],
            [0, 9, 9, 9, 0, 0, 0, 1, 9, 9, 9],
            [1, 9, 9, 9, 9, 9, 9, 9, 9, 0, 9],
            [0, 0, 9, 9, 0, 9, 1, 1, 9, 9, 9],
            [9, 9, 9, 1, 9, 0, 9, 0, 0, 9, 9],
            [0, 1, 9, 9, 0, 1, 9, 0, 9, 9, 9],
            [0, 1, 0, 0, 9, 9, 9, 0, 9, 9, 9],
            [9, 9, 9, 9, 1, 9, 9, 0, 0, 9, 9],
            [9, 9, 1, 9, 9, 1, 9, 9, 9, 0, 9],
            [9, 9, 9, 9, 0, 9, 0, 0, 1, 9, 9],
            [9, 1, 9, 9, 0, 1, 1, 0, 9, 9, 9],
            [1, 9, 9, 9, 0, 1, 0, 1, 9, 9, 9],
            [9, 9, 0, 0, 0, 1, 9, 9, 1, 9, 9],
            [1, 9, 0, 0, 9, 9, 9, 1, 1, 9, 9],
            [9, 9, 1, 0, 0, 0, 9, 9, 1, 9, 9],
            [1, 1, 0, 9, 9, 9, 9, 1, 0, 9, 9],
            [9, 0, 0, 9, 9, 9, 1, 0, 0, 9, 9],
            [0, 9, 9, 0, 1, 9, 1, 1, 9, 9, 9],
            [9, 0, 9, 9, 0, 0, 9, 0, 9, 9, 1],
            [1, 9, 1, 9, 9, 9, 1, 1, 0, 9, 9],
            [9, 9, 9, 9, 9, 1, 0, 9, 9, 0, 9],
            [0, 1, 1, 0, 9, 9, 0, 9, 9, 9, 9],
            [9, 9, 9, 0, 0, 9, 9, 0, 1, 9, 9],
            [0, 1, 9, 1, 9, 9, 1, 1, 1, 9, 9],
            [1, 0, 9, 9, 1, 9, 1, 1, 1, 9, 9],
            [9, 0, 9, 0, 0, 9, 9, 9, 1, 9, 9],
            [9, 0, 0, 0, 9, 9, 9, 9, 1, 9, 9],
            [9, 1, 9, 9, 0, 9, 1, 1, 0, 1, 9],
            [9, 1, 9, 1, 0, 9, 1, 1, 9, 9, 9],
            [9, 0, 0, 9, 9, 9, 0, 1, 0, 9, 9],
            [1, 1, 9, 1, 9, 9, 0, 0, 1, 9, 9],
            [9, 9, 1, 9, 9, 9, 9, 0, 9, 0, 9],
            [9, 1, 9, 9, 9, 0, 0, 0, 0, 9, 9],
            [9, 9, 9, 9, 9, 9, 9, 1, 9, 9, 0],
            [1, 9, 0, 9, 1, 0, 0, 1, 9, 9, 9],
            [1, 9, 1, 1, 9, 1, 0, 1, 9, 9, 9],
            [0, 1, 0, 1, 9, 0, 9, 1, 9, 9, 9],
            [1, 9, 0, 1, 1, 1, 1, 0, 9, 9, 9],
            [0, 1, 1, 9, 1, 1, 9, 1, 9, 9, 9],
            [1, 9, 1, 1, 1, 0, 1, 0, 9, 9, 9],
            [9, 9, 0, 9, 9, 0, 9, 9, 9, 0, 1]]
        for i in range(128):
            y += [xout[r][P[i]]]
        for i in range(32):
            X = list([])
            for j in range(4):
                X += [xin[r][4 * i + j]]
            for j in range(4):
                X += [y[4 * i + j]]
            X += [p[r][i]]
            X += [q[r][i]]
            X += [m[r][i]]
            for j in range(54):
                clauseseq = ""
                for k in range(11):
                    if (SymbolicCNFConstraintForSbox[j][k] == 1):
                        clauseseq += "-" + str(X[k] + 1) + " "
                    if (SymbolicCNFConstraintForSbox[j][k] == 0):
                        clauseseq += str(X[k] + 1) + " "
                clauseseq += "0" + "\n"
                file.write(clauseseq)
    
    # Add constraints for the original sequential encoding
    Main_Vars = list([])
    for r in range(Round):
        for i in range(32):
            Main_Vars += [p[Round - 1 - r][i]]
            Main_Vars += [q[Round - 1 - r][i]]
            Main_Vars += [m[Round - 1 - r][i]]
           
    Genobjectivefunction(Main_Vars, auxiliary_var_u, Main_Var_Num, CardinalityCons, file)
    file.close()
    # Call solver cadical
    #/home/user/program/lingeling/treengeling

    order = " /home/user/cadical-master/build/cadical " + "Present-Round" + str(Round) + "-Probability" + str(Probability) + ".cnf > Round" + str(Round) + "-Probability" + str(Probability) + "-solution.out"
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
    #order = "rm Present-Round" + str(Round) + "-Probability" + str(Probability) + ".cnf"
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











