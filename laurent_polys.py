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

  def __mul__(self, other):
    return ParamPoly(self.old_R, self.old_polynomial * other.old_polynomial, len(self.parameters))

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

def reduce_gcd(first, second):
  factors_first = first.factorize()
  factors_second = second.factorize()
  
  output1 = factors_first[0]
  for f in factors_first[1:]:
    if f not in factors_second:  output1 *= f

  output2 = factors_second[0]
  for f in factors_second[1:]:
    if f not in factors_first:  output2 *= f

  return output1, output2

def constraintsForLaurent(R, n, num, den):
  Num = ParamPoly(R, num, n)
  Den = ParamPoly(R, den, n)

  num_factors = Num.factorize()
  den_factors = Den.factorize()

  disjunct_cases = [[]]

  for gi in den_factors:
    new_disjunct_cases = []
    for dcase in disjunct_cases:
      if gi in num_factors:  continue
      new_disjunct_cases.append(dcase + [Num.old_polynomial % gi.old_polynomial] )
      for coeff in gi.coeffs_monoms():
        new_disjunct_cases.append(dcase + [gi.old_polynomial - (coeff[0]*coeff[1])] )
    disjunct_cases = new_disjunct_cases

  return disjunct_cases
