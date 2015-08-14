#!/bin/sh
''''exec python -- "$0" ${1+"$@"} # '''

from sage.all import *
import json
import sys
import ast
import traceback

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

def interp(req):
  cmd = req['cmd']
  if cmd == "GroebnerBasis":
    polylist = ast.literal_eval(req["equations"])
    if polylist == []:    return ""
    n_variables = len(polylist[0][0]) - 1 # The first element is the coefficient.
    R = PolynomialRing(QQ, n_variables, 'x')
    x = R.gens()
    polynomials = []
    for p in polylist:
      new_poly = 0
      for term in p:
        new_term = term[0]
        for i in range(n_variables):
          new_term *= x[i]**(term[i+1])
        new_poly += new_term
      polynomials.append(new_poly)
  
    reduced = ideal(polynomials).groebner_basis()
  
    # Make integer every constant. (Return this information!!!)
    reduced_int = []
    for p in reduced:
      denominators = [t.denominator() for t in p.coefficients()]
      reduced_int.append(p*lcm(denominators))
  
    reduced_polylist = []
    for p in reduced_int:
      reduced_poly = []
      coeffs = p.coefficients()
      mons = p.monomials()
      for i in range(len(mons)):
        reduced_term = [coeffs[i]]
        for j in range(len(x)):
          reduced_term.append(mons[i].degree(x[j]))
        reduced_poly.append(reduced_term)
      reduced_polylist.append(reduced_poly)
  
    # Print the output in Ocaml format.
    output = ""
    for i in range(len(reduced_polylist)):
      for j in range(len(reduced_polylist[i])):
        for k in range(len(reduced_polylist[i][j])):
          output += str(reduced_polylist[i][j][k])
          if (k < len(reduced_polylist[i][j])-1):    output += ","
        if (j < len(reduced_polylist[i])-1):    output += "t"
      if (i < len(reduced_polylist)-1):    output += "p"
  
    return output
  
  elif cmd == "reduceModulo":
    polylist = ast.literal_eval(req["equations"])
    n_equations = len(polylist)
    polylist += ast.literal_eval(req["polynomials"])
    n_variables = len(polylist[0][0]) - 1 # The first element is the coefficient.

    if n_variables == 0:    return ""

    R = PolynomialRing(QQ, n_variables, 'x')
    x = R.gens()
    polynomials = []
    for p in polylist:
      new_poly = 0*x[0]
      for term in p:
        new_term = term[0]
        for i in range(n_variables):
          new_term *= x[i]**(term[i+1])
        new_poly += new_term
      polynomials.append(new_poly)
      
    if n_equations == 0:
      reduced = polynomials[n_equations:]
    else:
      I = ideal(polynomials[:n_equations])  # We assume the input is already in groebner basis.    
      reduced = [poly.reduce(I) for poly in polynomials[n_equations:]]

    # Make integer every constant. (Return this information!!!)
    reduced_int = []
    for p in reduced:
      denominators = [t.denominator() for t in p.coefficients()]
      reduced_int.append(p*lcm(denominators))

    reduced_polylist = []
    for p in reduced_int:
      reduced_poly = []
      coeffs = p.coefficients()
      mons = p.monomials()
      for i in range(len(mons)):
        reduced_term = [coeffs[i]]
        for j in range(len(x)):
          reduced_term.append(mons[i].degree(x[j]))
        reduced_poly.append(reduced_term)
      if reduced_poly == []:
	reduced_polylist.append([[0*x[0]]*(len(x)+1)] )
      else:
        reduced_polylist.append(reduced_poly)

    # Print the output in Ocaml format.
    output = ""
    for i in range(len(reduced_polylist)):
      for j in range(len(reduced_polylist[i])):
        for k in range(len(reduced_polylist[i][j])):
          output += str(reduced_polylist[i][j][k])
          if (k < len(reduced_polylist[i][j])-1):    output += ","
        if (j < len(reduced_polylist[i])-1):    output += "t"
      if (i < len(reduced_polylist)-1):    output += "p"
  
    return output

def main():
  try:
    while True:
      #polylist = ast.literal_eval(sys.argv[1])
      inp = sys.stdin.readline()
      cmd = ast.literal_eval(inp)
      result = interp(cmd)
      o = json.dumps(result)
      #len = o.len()
      print(json.dumps(result))
      sys.stdout.flush()
        
  except Exception:
    traceback.print_exc()
      
if __name__ == "__main__":
    main()
 
