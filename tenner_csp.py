#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete the warehouse domain.  

'''
Construct and return Tenner Grid CSP models.
'''

from cspbase import *
import itertools

def get_row_constraints_binary(vars_row, values_row):
  '''
  returns row constraints in the form of binary constraints for a specified row
  '''
  row_cons = []
  for i in range(10):
      for j in range(i+1, 10):
          con = Constraint("C(T{},T{})".format(i,j),[vars_row[i], vars_row[j]])  
          sat_tuples = []
          for t in itertools.product(values_row[i], values_row[j]):
            if t[0] != t[1]:
              sat_tuples.append(t) 
          con.add_satisfying_tuples(sat_tuples)
          row_cons.append(con)
  return row_cons

def get_row_constraints(initial_tenner_board, vars, values):
  '''
  returns all row constraints in the form of n-ary constraints
  '''
  row_cons = []
  for i in range(len(initial_tenner_board[0])):
    scope = []
    possibilities = []
    for k in range(10):
      if len(values[i*10+k]) != 1:
        scope.append(vars[i*10+k])
        index = i*10+k
    con = Constraint("C(Trow{})".format(i),scope)  
    sat_tuples = []
    for t in itertools.permutations(*[values[index]]):
        sat_tuples.append(t)
    con.add_satisfying_tuples(sat_tuples)
    row_cons.append(con)
  return row_cons

def get_column_constraints(initial_tenner_board, vars, values):
  '''
  returns all column constraints in the form of n-ary constraints
  '''
  column_cons = []
  for i in range(10):
    scope = []
    possibilities = []
    for k in range(len(initial_tenner_board[0])):
      scope.append(vars[k*10+i])
      possibilities.append(values[k*10+i])
    con = Constraint("C(Tcolumn{})".format(i),scope)  
    sat_tuples = []
    for t in itertools.product(*possibilities):
      if sum(t) == initial_tenner_board[1][i]:
        sat_tuples.append(t)
    con.add_satisfying_tuples(sat_tuples)
    column_cons.append(con)
  return column_cons

def get_contigous_indexes(n):
  '''
  return all up/down and diagonal pairs of indicies
  '''
  indexes = []
  for i in range(n-1):
    for j in range(10):
      if j != 0:
        indexes.append([[i,j], [i+1,j-1]])
      if j != 9:
        indexes.append([[i,j], [i+1,j+1]])
      indexes.append([[i,j], [i+1,j]]) 
  return indexes

def get_contiguous_constraints(initial_tenner_board, vars, values):
  '''
  returns all contigous constraints in the form of binary constraints
  '''
  contiguous_cons = []
  indexes = get_contigous_indexes(len(initial_tenner_board[0]))
  for k in range(len(indexes)):
    scope = [vars[indexes[k][0][0]*10+indexes[k][0][1]], vars[indexes[k][1][0]*10+indexes[k][1][1]]]
    possibilities = [values[indexes[k][0][0]*10+indexes[k][0][1]], values[indexes[k][1][0]*10+indexes[k][1][1]]]
    con = Constraint("C(Tcontigous{},{})".format(indexes[k][0], indexes[k][1]),scope)  
    sat_tuples = []
    for t in itertools.product(*possibilities):
      if t[0] != t[1]:
        sat_tuples.append(t)
    con.add_satisfying_tuples(sat_tuples)
    contiguous_cons.append(con)
  return contiguous_cons

def tenner_csp_model_1(initial_tenner_board):
  '''Return a CSP object representing a Tenner Grid CSP problem along 
     with an array of variables for the problem. That is return

     tenner_csp, variable_array

     where tenner_csp is a csp representing tenner grid using model_1
     and variable_array is a list of lists

     [ [  ]
       [  ]
       .
       .
       .
       [  ] ]

     such that variable_array[i][j] is the Variable (object) that
     you built to represent the value to be placed in cell i,j of
     the Tenner Grid (only including the first n rows, indexed from 
     (0,0) to (n,9)) where n can be 3 to 8.
     
     
     The input board is specified as a pair (n_grid, last_row). 
     The first element in the pair is a list of n length-10 lists.
     Each of the n lists represents a row of the grid. 
     If a -1 is in the list it represents an empty cell. 
     Otherwise if a number between 0--9 is in the list then this represents a 
     pre-set board position. E.g., the board
  
     ---------------------  
     |6| |1|5|7| | | |3| |
     | |9|7| | |2|1| | | |
     | | | | | |0| | | |1|
     | |9| |0|7| |3|5|4| |
     |6| | |5| |0| | | | |
     ---------------------
     would be represented by the list of lists
     
     [[6, -1, 1, 5, 7, -1, -1, -1, 3, -1],
      [-1, 9, 7, -1, -1, 2, 1, -1, -1, -1],
      [-1, -1, -1, -1, -1, 0, -1, -1, -1, 1],
      [-1, 9, -1, 0, 7, -1, 3, 5, 4, -1],
      [6, -1, -1, 5, -1, 0, -1, -1, -1,-1]]
     
     
     This routine returns model_1 which consists of a variable for
     each cell of the board, with domain equal to {0-9} if the board
     has a 0 at that position, and domain equal {i} if the board has
     a fixed number i at that cell.
     
     model_1 contains BINARY CONSTRAINTS OF NOT-EQUAL between
     all relevant variables (e.g., all pairs of variables in the
     same row, etc.).
     model_1 also constains n-nary constraints of sum constraints for each 
     column.
  '''
  variable_array = []
  vars = []
  values = []
  for i in range(len(initial_tenner_board[0])):
    dom = [0,1,2,3,4,5,6,7,8,9]
    dom2 = [0,1,2,3,4,5,6,7,8,9]
    for j in range(10):
      if initial_tenner_board[0][i][j] != -1:
        dom2.remove(initial_tenner_board[0][i][j])
    for j in range(10):
      if initial_tenner_board[0][i][j] == -1:
        vars.append(Variable('V{},{}'.format(i,j), dom))
        values.append(dom2)
      else:
        vars.append(Variable('V{}{}'.format(i,j), [initial_tenner_board[0][i][j]]))
        values.append([initial_tenner_board[0][i][j]])
  cons = []
  cons += get_contiguous_constraints(initial_tenner_board, vars, values)
  for i in range(len(initial_tenner_board[0])):
    cons += get_row_constraints_binary(vars[i*10:i*10+10], values[i*10:i*10+10])
  cons += get_column_constraints(initial_tenner_board, vars, values)
  for i in range(len(initial_tenner_board[0])):
    variable_array.append(vars[10*i:10*i+10])
  csp = CSP("TENNER-M1", vars)
  for c in cons:
    csp.add_constraint(c)
  return csp, variable_array

##############################

def tenner_csp_model_2(initial_tenner_board):
  '''Return a CSP object representing a Tenner Grid CSP problem along 
     with an array of variables for the problem. That is return

     tenner_csp, variable_array

     where tenner_csp is a csp representing tenner using model_1
     and variable_array is a list of lists

     [ [  ]
       [  ]
       .
       .
       .
       [  ] ]

     such that variable_array[i][j] is the Variable (object) that
     you built to represent the value to be placed in cell i,j of
     the Tenner Grid (only including the first n rows, indexed from 
     (0,0) to (n,9)) where n can be 3 to 8.

     The input board takes the same input format (a list of n length-10 lists
     specifying the board as tenner_csp_model_1.
  
     The variables of model_2 are the same as for model_1: a variable
     for each cell of the board, with domain equal to {0-9} if the
     board has a -1 at that position, and domain equal {i} if the board
     has a fixed number i at that cell.

     However, model_2 has different constraints. In particular,
     model_2 has a combination of n-nary 
     all-different constraints and binary not-equal constraints: all-different 
     constraints for the variables in each row, binary constraints for  
     contiguous cells (including diagonally contiguous cells), and n-nary sum 
     constraints for each column. 
     Each n-ary all-different constraint has more than two variables (some of 
     these variables will have a single value in their domain). 
     model_2 should create these all-different constraints between the relevant 
     variables.
  '''
  variable_array = []
  vars = []
  values = []
  for i in range(len(initial_tenner_board[0])):
    dom = [0,1,2,3,4,5,6,7,8,9]
    dom2 = [0,1,2,3,4,5,6,7,8,9]
    for j in range(10):
      if initial_tenner_board[0][i][j] != -1:
        dom2.remove(initial_tenner_board[0][i][j])
    for j in range(10):
      if initial_tenner_board[0][i][j] == -1:
        vars.append(Variable('V{},{}'.format(i,j), dom))
        values.append(dom2)
      else:
        vars.append(Variable('V{}{}'.format(i,j), [initial_tenner_board[0][i][j]]))
        values.append([initial_tenner_board[0][i][j]])
  cons = []
  cons += get_contiguous_constraints(initial_tenner_board, vars, values)
  cons += get_row_constraints(initial_tenner_board, vars, values)
  cons += get_column_constraints(initial_tenner_board, vars, values)
  for i in range(len(initial_tenner_board[0])):
    variable_array.append(vars[10*i:10*i+10])
  csp = CSP("TENNER-M2", vars)
  for c in cons:
    csp.add_constraint(c)
  return csp, variable_array
