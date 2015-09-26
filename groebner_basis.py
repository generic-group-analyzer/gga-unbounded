#!/bin/sh
''''exec python -- "$0" ${1+"$@"} # '''

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
        new_term *= x[i]**(term[i+1])
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
        #term.append(mons[i].degree(x[j]))
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
    p += 0*R.gens()[0]   # If we had a constant, not it is a polynomial.
    common_den = lcm([t.denominator() for t in p.coefficients()])
    new_polys.append(p * common_den)
    max_den = max(max_den, abs(common_den))
  return new_polys, max_den

def interp(req):
  cmd = req['cmd']
  if cmd == "GroebnerBasis":
    polylist = ast.literal_eval(req["equations"])
    if polylist == []:    return "B1"
    n_variables = len(polylist[0][0]) - 1    # The first element is the coefficient.
    if (n_variables == 0): return "B1"

    R = PolynomialRing(QQ, n_variables, 'x')

    polynomials = polys_of_polylist(polylist, R)
    reduced = ideal(polynomials).groebner_basis()
  
    # Make integer every coefficient. (Return this information!!!)
    reduced, common_den = integer_coefficients(reduced, R)
     
    reduced_polylist = polys_to_polylist(reduced, R)
  
    # Print the output in Ocaml format.
    return polylist_to_Ocaml(reduced_polylist) + "B" + str(abs(common_den))
  
  elif cmd == "reduceModulo":
    polylist = ast.literal_eval(req["equations"])
    n_equations = len(polylist)
    polylist += ast.literal_eval(req["polynomials"])
    n_variables = len(polylist[0][0]) - 1    # The first element is the coefficient.
    if n_variables == 0:    return "B1"

    R = PolynomialRing(QQ, n_variables, 'x')

    polynomials = polys_of_polylist(polylist, R)

    if n_equations == 0:  reduced = polynomials[n_equations:]
    else:
      I = ideal(polynomials[:n_equations])  # We assume the input is already in groebner basis.
      reduced = [poly.reduce(I) for poly in polynomials[n_equations:]]

    # Make integer every coefficient. (Return this information!!!)
    reduced, common_den = integer_coefficients(reduced, R)
 
    reduced_polylist = polys_to_polylist(reduced, R)

    # Print the output in Ocaml format.
    return polylist_to_Ocaml(reduced_polylist) + "B" + str(abs(common_den))

  elif cmd == "NumDen":
    num = ast.literal_eval(req["num"])
    den = ast.literal_eval(req["den"])
    n = ast.literal_eval(req["params"])

    if num == []: return "B1"
    n_variables = len(num[0]) - 1 # The first element is the coefficient.
    if n_variables == 0:    return "B1"

    R = PolynomialRing(QQ, n_variables, 'x')

    num, den = polys_of_polylist([num, den], R)
    old_num = num
    old_den = den
    num_num = num.numerator()
    num_den = num.denominator()
    den_num = den.numerator()
    den_den = den.denominator()
    num = num_num * den_den
    den = num_den * den_num

    constrs = constraintsForLaurent(R, n, num, den)
    constrs = filter_constraints(constrs, R)
    
    quotients = []
    max_common = 1
    for c in constrs:
      I = ideal(c)
      if old_den.reduce(I) == 0:
        quotients.append("E")
      else:
        q,r = old_num.reduce(I).quo_rem(old_den.reduce(I))
        q,common = integer_coefficients([q],R)
        max_common = max(max_common, abs(common))
        polylist = polys_to_polylist(q,R)
        quotients.append(polylist_to_Ocaml(polylist))

    # Make integer every coefficient. (Return this information!!!)
    new_constrs = []
    for c in constrs:
      c, common_den = integer_coefficients(c, R)
      new_constrs.append(c)

    constrs_polylist = []
    for c in new_constrs:
      constrs_polylist.append(polys_to_polylist(c,R))

    # Print the output in Ocaml format.
    output_list = []
    for polylist in constrs_polylist:
      output_list.append(polylist_to_Ocaml(polylist))

    output = ""
    for i in range(len(output_list)):
      output += output_list[i] + "m" + quotients[i] + "r"

    return output[:-1] + "B" + str(max_common)

def main():
  try:
    while True:
      inp = sys.stdin.readline()
      if (inp == ''): break
      cmd = ast.literal_eval(inp)
      result = interp(cmd)
      o = json.dumps(result)
      print(json.dumps(result))
      sys.stdout.flush()
        
  except Exception:
    traceback.print_exc()
      
if __name__ == "__main__":
    main()
 
