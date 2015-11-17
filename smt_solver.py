#!/bin/sh
''''exec python -- "$0" ${1+"$@"} # '''

from z3 import *
import json
import sys
import ast
import traceback

def check_feasibility(matrix, vector):
    Lambda = []
    n_lambda = len(matrix[0])
    s = Solver()
    for i in range(n_lambda):
        Lambda.append(Int('Lambda' + str(i+1)) )
        s.add(Lambda[i] >= 0)
        
    for i in range(len(vector)):
        expression = 0
        for j in range(n_lambda):
            expression += matrix[i][j] * Lambda[j]

        s.add(expression == vector[i])

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

	cmd = ast.literal_eval(inp)
        M = cmd["matrix"]
        v = cmd["vector"]
        if len(M) == 0:
          result = v == []
        elif len(M[0]) == 0:
          result = not any(v)	   
        else:	     
          result = check_feasibility(M, v)	
     
        print(json.dumps(result))
        sys.stdout.flush()
	    
    except Exception:
        traceback.print_exc()
      
if __name__ == "__main__":
    main()
 

