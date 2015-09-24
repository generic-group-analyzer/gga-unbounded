#!/bin/sh
''''exec python -- "$0" ${1+"$@"} # '''

from sage.all import *

def unique(seq):
   # not order preserving
   set = {}
   map(set.__setitem__, seq, [])
   return set.keys()

class ParamPoly(object):
  def __init__(self, R, p, n):
    self.old_R = R
    self.old_polynomial = p
    self.P = PolynomialRing(QQ, R.gens()[:n])
    self.V = PolynomialRing(self.P, R.gens()[n:])
    self.parameters = self.P.gens()
    self.variables = self.V.gens()
    self.polynomial = self.poly2parampoly(R,self.P,self.V,p)
    
  def poly2parampoly(self, R,P,V, polynomial):
    variables = R.gens()
    new_variables = P.gens() + V.gens()

    coeffs = polynomial.coefficients()
    monoms = polynomial.monomials()
  
    poly = 0
    for i in range(len(coeffs)):
      term = coeffs[i]
      for j in range(len(variables)):
        term *= new_variables[j]**(monoms[i].degree(monoms[i].parent()(variables[j])))
      poly += term

    return poly

  def coeffs_monoms(self):
    old_coeffs = self.old_polynomial.coefficients()
    old_monoms = self.old_polynomial.monomials()
    output = []
    for i in range(len(old_monoms)):
      new_coeff = old_coeffs[i]
      new_monom = 1
      for p in self.old_R.gens()[:(len(self.parameters))]:
        new_coeff *= p**(old_monoms[i].degree(old_monoms[i].parent()(p)))
      for v in self.old_R.gens()[(len(self.parameters)):]:
        new_monom *= v**(old_monoms[i].degree(old_monoms[i].parent()(v)))
      output.append((new_coeff, new_monom))
    output_monoms = [m for (c,m) in output]
    new_output = []
    for m in sorted(unique(output_monoms)):
      new_coeff = 0
      for (C,M) in output:
        if (m == M):  new_coeff += C
      new_output.append((new_coeff, m))
    return new_output

  def factorize(self):
    factors = self.old_polynomial.factor()
    new_factors = []
    for i in range(len(factors)):
        new_factors += [factors[i][0] for j in range(factors[i][1])]
    return [ParamPoly(self.old_R, f, len(self.parameters)) for f in new_factors]
    
  def __str__(self):
    return str(self.polynomial)


def matchingFactor(f1,f2):
  constrs = []
  for (coeffs1, monoms1) in f1.coeffs_monoms():
    new_constr = coeffs1
    for (coeffs2, monoms2) in f2.coeffs_monoms():
      if (monoms1 == monoms2):
        new_constr -= coeffs2
        break
    constrs.append(new_constr)
  for (coeffs2, monoms2) in f2.coeffs_monoms():
    new_constr = -coeffs2
    for (coeffs1, monoms1) in f1.coeffs_monoms():
      if (monoms2 == monoms1):
        new_constr += coeffs1
        break
    constrs.append(new_constr)
  return unique(constrs)


def constraintsForLaurent(R, n, num, den):
  Num = ParamPoly(R, num, n)
  Den = ParamPoly(R, den, n)
  
  num_factors = Num.factorize()
  den_factors = Den.factorize()

  all_cases = [([], num_factors)]    # No restrictions and all the numerator factors are available.

  alternative_cases = []
  for f in num_factors:
    alternative_cases.append((matchingFactor(f,ParamPoly(R,0*R.gens()[0],n)) ,[]))
    
  for f in den_factors:
    coeffs = [eq for (eq, mon) in f.coeffs_monoms()]
    if len(coeffs) > 1:   # We need to reduce this factor.
      new_all_cases = []
      new_constrs = sorted([coeffs[:i] + coeffs[i+1:] for i in range(len(coeffs))])
      for (constr, factors) in all_cases:
        for new in new_constrs:
          new_all_cases.append((new + constr, factors))
          
      for (constrs, factors) in all_cases:
        for j in range(len(factors)):
          new_all_cases.append((matchingFactor(f, factors[j]) + constrs, factors[:j] + factors[j+1:]))
      
      all_cases = new_all_cases
      
    else:
      alternative_cases.append(([f.old_polynomial],[]))

  return [constr for (constr, f) in (all_cases+alternative_cases)]


def filter_constraints(constraints, R):
  constraints = [R.ideal(c).groebner_basis() for c in constraints]  
  output = []
  for c in constraints:
    new_c = []
    for conj in c:
      if (conj == 0):    continue
      if (conj.monomials() == [1]):
          new_c = []
          break
      new_c.append(conj)
    if new_c != []:
      output.append(new_c)
  return output
