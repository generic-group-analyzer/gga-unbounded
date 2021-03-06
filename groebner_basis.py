#!/usr/bin/env sage

from sage.all import *
import json
import sys
import ast
import traceback

from laurent_polys import *

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

def polys_of_polylist(polylist, R):
  x = R.gens()
  polynomials = []
  for p in polylist:
    new_poly = 0*x[0]
    for term in p:
      new_term = term[0]
      for i in range(len(x)):
        new_term *= x[i]**(term[1][i])
      new_poly += new_term
    polynomials.append(new_poly)
  return polynomials

def polys_to_polylist(polys, R):
  x = R.gens()
  polylist = []
  for p in polys:
    poly = []
    coeffs = p.coefficients()
    mons = p.monomials()
    for i in range(len(mons)):
      term = [coeffs[i]]
      for j in range(len(x)):
        term.append(mons[i].degree(mons[i].parent()(x[j])))
      poly.append(term)
    if poly == []:  polylist.append([[0*x[0]]*(len(x)+1)] )
    else: polylist.append(poly)
  return polylist

def polylist_to_Ocaml(polylist):
  output = ""
  for i in range(len(polylist)):
    for j in range(len(polylist[i])):
      for k in range(len(polylist[i][j])):
        output += str(polylist[i][j][k])
        if (k < len(polylist[i][j])-1):    output += ","
      if (j < len(polylist[i])-1):    output += "t"
    if (i < len(polylist)-1):    output += "p"
  return output

def integer_coefficients(polynomials, R):
  new_polys = []
  max_den = 1
  for p in polynomials:
    p += 0*R.gens()[0]
    common_den = lcm([t.denominator() for t in p.coefficients()])
    new_polys.append(p * common_den)
    max_den = max(max_den, abs(common_den))
  return new_polys, max_den

def interp(req):
  cmd = req['cmd']
  if cmd == "GroebnerBasis":
    polylist = req["system"]
    if polylist == []:     return ""
    n_variables = len(polylist[0][0][1])
    if (n_variables == 0): return ""

    R = PolynomialRing(QQ, n_variables, 'x')

    polynomials = polys_of_polylist(polylist, R)
    reduced = ideal(polynomials).groebner_basis()

    # Make integer every coefficient. (Return this information!!!)
    reduced, common_den = integer_coefficients(reduced, R)
    reduced_polylist = polys_to_polylist(reduced, R)
  
    # Print the output in Ocaml format.
    return polylist_to_Ocaml(reduced_polylist)
  
  elif cmd == "reduce":
    polylist = req["system"]
    to_reduce = req["to_reduce"]
    if polylist == []:      return ""
    n_equations = len(polylist)    
    n_variables = len(polylist[0][0][1]) 
    if n_variables == 0:    return ""

    R = PolynomialRing(QQ, n_variables, 'x')

    polynomials = polys_of_polylist(polylist, R)
    to_reduce = polys_of_polylist([to_reduce], R)[0]

    if n_equations == 0:
        reduced = to_reduce
    else:
        I = ideal(polynomials)
        reduced = to_reduce.reduce(I)

    # Make integer every coefficient. (Return this information!!!)
    reduced, common_den = integer_coefficients([reduced], R) 
    reduced_poly = polys_to_polylist(reduced, R)[0]

    # Print the output in Ocaml format.
    return polylist_to_Ocaml([reduced_poly])

  elif cmd == "Laurent":
    polylist = [req["f"], req["g"]]
    n_variables = len(polylist[0][0][1])
    n_params = req["nparams"]
    
    R = PolynomialRing(QQ, n_variables, 'x')

    for i in range(len(polylist)):
      for j in range(len(polylist[i])):
          for k in range(len(polylist[i][j][1])):
            d = polylist[i][j][1][k]
            if (d < 0):
                for j1 in range(len(polylist[0])):
                  polylist[0][j1][1][k] -= d
                for j1 in range(len(polylist[1])):
                  polylist[1][j1][1][k] -= d


    polynomials = polys_of_polylist(polylist, R)
    f = polynomials[0]
    g = polynomials[1]

    disjunction_cases = constraintsForLaurent(R, n_params, f, g)

    disj_polylist = []
    for conj in disjunction_cases:
      disj_polylist.append(polys_to_polylist(conj,R))

    # Print the output in Ocaml format.
    output_list = []
    for conj in disj_polylist:
      output_list.append(polylist_to_Ocaml(conj))

    output = ""
    for i in range(len(output_list)):
      output += output_list[i] + "|"

    return output[:-1]

  elif cmd == "factor":
    f = req["f"]

    if f == []:  return ""

    n_variables = len(f[0][1]) 
    if n_variables == 0:    return str(f[0][0])

    R = PolynomialRing(QQ, n_variables, 'x')

    for j in range(len(f)):
      for k in range(len(f[j][1])):
        d = f[j][1][k]
        if (d < 0):
          for j1 in range(len(f)):
            f[j1][1][k] -= d

    f = polys_of_polylist([f], R)[0]

    factors = [factor[0] for factor in f.factor()]

    # Make integer every coefficient. (Return this information!!!)
    factors, common_den = integer_coefficients(factors, R)
    factors = polys_to_polylist(factors, R)

    # Print the output in Ocaml format.
    return polylist_to_Ocaml(factors)

def main():
  hashTable = {}
  try:
    while True:
      inp = sys.stdin.readline()
      if (inp == ''): break
      try:
        result = hashTable[inp]
      except Exception:
        cmd = ast.literal_eval(inp)
        result = interp(cmd)
        hashTable[inp] = result

      o = json.dumps(result)
      print(json.dumps(result))
      sys.stdout.flush()
        
  except Exception:
    traceback.print_exc()
      
if __name__ == "__main__":
    main()
 
