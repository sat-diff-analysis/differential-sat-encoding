import os
import time
import random

FullRound = 20

SearchRoundStart =19
SearchRoundEnd = 20
InitialLowerBound = 188


DifferentialProbabilityBound = list([])
for i in range(FullRound):
    DifferentialProbabilityBound += [0]
    

    
def CountClausesInRoundFunction(Round, Probability, clause_num):
    count = clause_num
    # Nonzero input
    count += 1
    # Cluases for Round function
    for r in range(Round):
        #Clauses for Sboxes
        for nibble in range(16):
            count += 57
        #Clauses for MDS
        if r<Round-1:
            for j in range (16):
                for i in range(4): 
                    count += 8
        #Clauses for Permutation
        
    return count
    
def CountClausesInSequentialEncoding(main_var_num, cardinalitycons, clause_num):
    count = clause_num
    n = main_var_num
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
    
    
def GenSequentialEncoding(x, u, main_var_num, cardinalitycons, fout):
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
            

            
def Decision(Round, Probability, flag):
    TotalProbability = 16 * Round * 3
    count_var_num = 0;
    time_start = time.time()
    # Declare variable
    xin = []
    sout = []
    p = []
    q = []
    m = []
    xout = []
    for i in range(Round):
        xin.append([])
        sout.append([])
        p.append([])
        q.append([])
        m.append([])
        xout.append([])
        for j in range(64):
            xin[i].append(0)
        for j in range(64):
            sout[i].append(0)
        for j in range(16):
            p[i].append(0)
            q[i].append(0)
            m[i].append(0)
        for j in range(64):
            xout[i].append(0)
    # Allocate variables
    for i in range(Round):
        for j in range(64):
            xin[i][j] = count_var_num
            count_var_num += 1
        for j in range(64):
            sout[i][j] = count_var_num
            count_var_num += 1
        for j in range(16):
            p[i][j] = count_var_num
            count_var_num += 1
        for j in range(16):
            q[i][j] = count_var_num
            count_var_num += 1
        for j in range(16):
            m[i][j] = count_var_num
            count_var_num += 1
    for i in range(Round - 1):
        for j in range(64):
            xout[i][j] = xin[i + 1][j]
    for i in range(64):
        xout[Round - 1][i] = count_var_num
        count_var_num += 1
    auxiliary_var_u = []
    for i in range(TotalProbability - 1):
        auxiliary_var_u.append([])
        for j in range(Probability):
            auxiliary_var_u[i].append(count_var_num)
            count_var_num += 1
    # Count the number of clauses in the round function
    count_clause_num = 0
    count_clause_num = CountClausesInRoundFunction(Round, Probability, count_clause_num)
    # Count the number of clauses in the original sequential encoding
    Main_Var_Num = 16 * Round * 3
    CardinalityCons = Probability
    count_clause_num = CountClausesInSequentialEncoding(Main_Var_Num, CardinalityCons, count_clause_num)
    # Open file
    file = open("Problem-Round" + str(Round) + "-Probability" + str(Probability) + ".cnf", "w")
    file.write("p cnf " + str(count_var_num) + " " + str(count_clause_num) + "\n")
    # Add constraints to claim nonzero input difference
    clauseseq = ""
    for i in range(64):
        clauseseq += str(xin[0][i] + 1) + " "
    clauseseq += "0" + "\n"
    file.write(clauseseq)
    # Add constraints for the round function
    Pi=[0, 1, 2, 3, 28, 29, 30, 31, 56, 57, 58, 59, 36, 37, 38, 39, 20, 21, 22, 23, 8, 9, 10, 11, 44, 45, 46, 47, 48, 49, 50, 51, 60, 61, 62, 63, 32, 33, 34, 35, 4, 5, 6, 7, 24, 25, 26, 27, 40, 41, 42, 43, 52, 53, 54, 55, 16, 17, 18, 19, 12, 13, 14, 15]
    SymbolicCNFConstraintForSbox = [# Differential Probability Midori64:57 constraints
        [9, 9, 1, 0, 9, 0, 1, 9, 1, 9, 9],
        [9, 0, 1, 9, 9, 9, 1, 0, 1, 9, 9],
        [0, 0, 0, 9, 1, 9, 9, 1, 9, 9, 9],
        [1, 9, 9, 1, 0, 0, 0, 9, 9, 9, 9],
        [0, 9, 0, 0, 1, 1, 9, 9, 9, 9, 9],
        [1, 1, 9, 9, 0, 9, 0, 0, 9, 9, 9],
        [9, 0, 1, 9, 9, 0, 1, 9, 1, 9, 9],
        [9, 9, 1, 0, 9, 9, 1, 0, 1, 9, 9],
        [9, 1, 9, 1, 9, 1, 9, 1, 1, 9, 9],
        [9, 9, 0, 9, 1, 1, 9, 1, 9, 9, 9],
        [1, 1, 9, 1, 9, 9, 0, 9, 9, 9, 9],
        [9, 9, 9, 9, 9, 9, 9, 9, 9, 0, 1],
        [9, 9, 9, 9, 9, 9, 9, 9, 1, 9, 0],
        [9, 9, 9, 9, 9, 9, 1, 9, 9, 9, 0],
        [9, 0, 9, 1, 9, 9, 0, 9, 0, 9, 9],
        [9, 9, 0, 9, 9, 1, 9, 0, 0, 9, 9],
        [9, 9, 9, 9, 1, 9, 9, 9, 9, 9, 0],
        [9, 9, 9, 9, 9, 0, 1, 0, 1, 9, 9],
        [9, 9, 0, 9, 9, 9, 0, 1, 0, 9, 9],
        [9, 1, 9, 0, 9, 9, 0, 9, 0, 9, 9],
        [1, 9, 9, 9, 9, 9, 0, 0, 0, 9, 9],
        [9, 1, 9, 1, 0, 9, 9, 0, 0, 9, 9],
        [9, 9, 1, 9, 9, 9, 9, 9, 9, 9, 0],
        [9, 0, 9, 0, 9, 0, 0, 0, 9, 1, 9],
        [9, 0, 0, 0, 9, 9, 9, 9, 0, 9, 1],
        [9, 1, 9, 0, 9, 1, 9, 1, 0, 9, 9],
        [9, 9, 0, 9, 9, 0, 9, 1, 0, 9, 9],
        [9, 0, 9, 0, 9, 1, 9, 1, 1, 9, 9],
        [9, 1, 9, 1, 9, 0, 9, 1, 0, 9, 9],
        [1, 9, 9, 0, 9, 0, 9, 1, 0, 9, 9],
        [0, 9, 1, 9, 1, 9, 1, 9, 0, 9, 9],
        [9, 0, 9, 1, 9, 1, 9, 1, 0, 9, 9],
        [9, 9, 1, 9, 0, 1, 1, 1, 0, 9, 9],
        [9, 0, 1, 9, 0, 0, 1, 9, 9, 9, 9],
        [9, 9, 1, 0, 0, 1, 0, 9, 1, 9, 9],
        [9, 0, 1, 9, 0, 9, 0, 1, 1, 9, 9],
        [9, 9, 0, 9, 9, 1, 1, 1, 1, 9, 9],
        [9, 9, 9, 9, 0, 0, 9, 0, 1, 9, 9],
        [0, 0, 9, 0, 9, 9, 9, 9, 1, 9, 9],
        [9, 1, 1, 1, 9, 9, 0, 9, 1, 9, 9],
        [1, 0, 9, 1, 9, 1, 1, 0, 9, 9, 9],
        [9, 0, 9, 0, 9, 1, 1, 0, 0, 9, 9],
        [9, 1, 1, 0, 0, 9, 9, 0, 9, 9, 9],
        [9, 1, 9, 0, 1, 0, 9, 9, 0, 9, 9],
        [9, 0, 9, 1, 1, 9, 9, 0, 0, 9, 9],
        [9, 9, 1, 0, 1, 0, 9, 1, 1, 9, 9],
        [9, 0, 1, 9, 1, 1, 9, 0, 1, 9, 9],
        [9, 9, 9, 1, 1, 1, 9, 0, 0, 9, 9],
        [0, 1, 0, 9, 9, 9, 1, 0, 1, 9, 9],
        [0, 9, 0, 1, 9, 0, 1, 9, 1, 9, 9],
        [9, 1, 9, 1, 9, 0, 0, 0, 9, 9, 9],
        [0, 0, 9, 9, 9, 1, 9, 1, 0, 9, 9],
        [1, 1, 0, 0, 0, 0, 9, 9, 1, 9, 9],
        [0, 9, 0, 0, 1, 9, 0, 1, 9, 9, 9],
        [0, 0, 0, 9, 1, 1, 0, 9, 9, 9, 9],
        [1, 9, 0, 1, 0, 9, 0, 0, 9, 9, 9],
        [1, 1, 9, 0, 9, 0, 1, 1, 9, 9, 9]]
    
    
    for r in range(Round):
        for nibble in range(16):
            X = list([])
            for i in range(4):
                X += [xin[r][4 * nibble + i]]
            for i in range(4):
                X += [sout[r][Pi[4 * nibble + i]]]
            X += [p[r][nibble]]
            X += [q[r][nibble]]
            X += [m[r][nibble]]
            for i in range(57):
                clauseseq = ""
                for k in range(11):
                    if (SymbolicCNFConstraintForSbox[i][k] == 1):
                        clauseseq += "-" + str(X[k] + 1) + " "
                    if (SymbolicCNFConstraintForSbox[i][k] == 0):
                        clauseseq += str(X[k] + 1) + " "
                clauseseq += "0" + "\n"
                file.write(clauseseq)
        if r<Round-1:
            for j in [0,1,2,3,16,17,18,19,32,33,34,35,48,49,50,51]:
                for i in range(4): 
                    XorInput =[sout[r][j + 4*((i+1)%4)],sout[r][ j + 4*((i+2)%4)],sout[r][ j + 4*((i+3)%4)]]
                    a = XorInput[0]
                    b = XorInput[1]
                    c= XorInput[2]
                    d= xout[r][j+4*i]

                    clauseseq = str(a + 1) + " " + str(b + 1) + " " + str(c + 1) + " " + "-" + str(d + 1)+" " + "0" + "\n"
                    file.write(clauseseq)
                    clauseseq = str(a + 1) + " " + str(b + 1) + " " + "-" + str(c + 1) + " " + str(d + 1)+" " + "0" + "\n"
                    file.write(clauseseq)
                    clauseseq = str(a + 1) + " " + "-" + str(b + 1) + " " + str(c + 1) + " " + str(d + 1)+" " + "0" + "\n"
                    file.write(clauseseq)
                    clauseseq = "-" + str(a + 1) + " " + str(b + 1) + " " + str(c + 1) + " " + str(d + 1)+" " + "0" + "\n"
                    file.write(clauseseq)

                    clauseseq = str(a + 1) + " " + "-" + str(b + 1) + " " + "-" + str(c + 1) + " " + "-" + str(d + 1)+" " + "0" + "\n"
                    file.write(clauseseq)
                    clauseseq = "-" + str(a + 1) + " " + str(b + 1) + " " + "-" + str(c + 1) + " " + "-" + str(d + 1)+" " + "0" + "\n"
                    file.write(clauseseq)
                    clauseseq = "-" + str(a + 1) + " " + "-" + str(b + 1) + " " + str(c + 1) + " " + "-" + str(d + 1)+" " + "0" + "\n"
                    file.write(clauseseq)
                    clauseseq = "-" + str(a + 1) + " " + "-" + str(b + 1) + " " + "-" + str(c + 1) + " " + str(d + 1)+" " + "0" + "\n"
                    file.write(clauseseq)

        
    # Add constraints for the original sequential encoding
    Main_Vars = list([])
    for r in range(Round):
        for i in range(16):
            Main_Vars += [p[Round - 1 - r][i]]
            Main_Vars += [q[Round - 1 - r][i]]
            Main_Vars += [m[Round - 1 - r][i]]
    GenSequentialEncoding(Main_Vars, auxiliary_var_u, Main_Var_Num, CardinalityCons, file)
    
    file.close()
    # Call solver cadical
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
        flag = Decision(totalround, CountProbability,  flag)
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
