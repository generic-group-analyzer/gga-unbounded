#!/bin/sh
''''exec python -- "$0" ${1+"$@"} # '''

from z3 import *
import json
import sys
import ast
import traceback

def check_feasibility(matrix, vector, n_lambda, n_indices):
    Lambda = []
    Delta = []
    if (n_indices == 0):
        n_delta = (len(matrix[0]))
    else:
        n_delta = (len(matrix[0]) - n_lambda)/n_indices

    s = Solver()
    for i in range(n_lambda):
        Lambda.append(Int('Lambda' + str(i+1)) )
        s.add(Lambda[i] >= 0)
        
    for i in range(n_delta * n_indices):
        Delta.append(Int('Delta' + str(i+1)) )
        s.add(Delta[i] >= 0)
        s.add(Delta[i] <= 1)

    for i in range(len(vector)):
        expression = 0
        for j in range(n_lambda):
            expression += matrix[i][j] * Lambda[j]

        for j in range(n_delta * n_indices):
            expression += matrix[i][n_lambda + j] * Delta[j]

        s.add(expression == vector[i])

    if n_delta > 0:
        for idx in range(n_indices):
            expression = 0
            for j in range(n_delta):
                expression += expression + Delta[j+idx*n_delta]        
            s.add(expression <= 1)

    return s.check() == sat


def _parseJSON(obj):
  """Convert unicode strings to standard strings"""
  if isinstance(obj, dict):
      newobj = {}
      for key, value in obj.iteritems():
          key = str(key)
          newobj[key] = _parseJSON(value)
  elif isinstance(obj, list):
      newobj = []
      for value in obj:
          newobj.append(_parseJSON(value))
  elif isinstance(obj, unicode):
      newobj = str(obj)
  else:
      newobj = obj
  return newobj


def main():
    try:
      while True:
        inp = sys.stdin.readline()
	if (inp == ''): break
	systems_list = ast.literal_eval(inp)
	result = False

	for system in systems_list:
            cmd = ast.literal_eval(system)
            M = cmd["matrix"]
            v = cmd["vector"]
            n_lambda = cmd["lambda"]
            n_indices = cmd["indices"]
	    if len(M) == 0:
	       result = v == []
            elif len(M[0]) == 0:
                result = not any(v)	   
            else:	     
                result = check_feasibility(M, v, n_lambda, n_indices)	
	    if result:
	       break

        print(json.dumps(result))
        sys.stdout.flush()
	    
    except Exception:
        traceback.print_exc()
      
if __name__ == "__main__":
    main()
 

