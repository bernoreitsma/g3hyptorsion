/* This file contains point functions on the jacobian.
	Points: Given J, pol, d, computes a set of points on J of the form J ! [pol, ***, d].
	~~~Points() could be faulty when degree(f) == 8: It seems like an infinite recursion!~~~
	ToJacobian: Given J, A, B, C s.t. f = B^2 - A*C, return J ! [A,B, Degree(A)].
*/

Attach("G3HypHelp.m");
import "G3HypHelp.m": K3quartics, K3deltas, Xipolynomials, K3biquforms, K3xi2coeffs;

// We store the data with the curve

declare attributes CrvHyp:
 KummerEquations, KummerVariety, KummerDeltas, KummerXipols, KummerBQF, HeightTable;

declare verbose ReducedBasis, 2;

declare verbose FindPointsG3, 3;

forward ToJacobian;

intrinsic Points(J::JacHyp, pol::RngUPolElt : d := Degree(pol)) -> SetIndx[JacHypPt]
{Returns as an indexed set all points on the hyperelliptic Jacobian J whose first component
is the given polynomial pol and whose last component is d.}
	// require basic conditions for Mumford Representation.
  require d le Dimension(J): "The degree cannot be larger than the genus.";
  fact := Factorization(pol);
  f, h := HyperellipticPolynomials(Curve(J));
  require h eq 0: "Need a curve of the form y^2 = f(x).";
  require d ge Degree(pol): "d must be >= deg(pol).";
  
  if d gt Degree(pol) then
    require IsEven(Degree(f)): "d > deg(pol) ==> no Weierstrass point at infinity.";
  end if;
  if IsOdd(d) then
    require IsOdd(Degree(f)): "odd d ==> need Weierstrass point at infinity.";
  end if;
  R := BaseRing(J);
  if IsOdd(Degree(f)) or forall{a : a in fact | IsEven(Degree(a[1]))} then
    ptsJ := [];
    for a in fact do
      if Degree(a[1]) eq 1 then
        flag, b := IsSquare(Evaluate(f, -Coefficient(a[1],0)/Coefficient(a[1],1)));
        if not flag then return {@ @}; end if; // no point possible
				bpol := Parent(a[1])![b];
        Append(~ptsJ, a[2]*ToJacobian(J, a[1], bpol, ExactQuotient(bpol^2 - f, a[1])));
      else;
        K := ext<R | a[1]>;
        assert Evaluate(a[1], K.1) eq 0;
        flag, b := IsSquare(Evaluate(f, K.1));
        if not flag then return {@ @}; end if; // no point possible
				bpol := Parent(a[1])!Eltseq(b);
        Append(~ptsJ, a[2]*ToJacobian(J, a[1], bpol, ExactQuotient(bpol^2 - f, a[1])));
      end if;
    end for;
    if d gt Degree(pol) then
      ptsinf := PointsAtInfinity(Curve(J));
      if #ptsinf ne 2 then return {@ @}; end if;
      Append(~ptsJ, ExactQuotient(d - Degree(pol), 2)*(ptsinf[1] - ptsinf[2]));
    end if;
    // combine
    result := {@ J!0 @};
    for pt in ptsJ do
      result := {@ rpt + pt : rpt in result @} join {@ rpt - pt : rpt in result @};
    end for;
    return {@ pt : pt in result | pt[1] eq pol and pt[3] eq d @};
  else
    if Dimension(J) eq 2 then			// dimension = g, so this should call the function for genus 2 (?)
      return Points(J, pol, d);
    end if;
    // should work in Pic/<m>
    require false: "This case is not yet implemented.";
		
  end if;
end intrinsic;

import "BalancedDivisor.m": Precompute, Reduce, Adjust;

function ToJacobian(J, Apol, Bpol, Cpol);
  /*f := Bpol^2 - Apol*Cpol;
	if Degree(f) eq 8 then
		V := Precompute(f);
		if Degree(Apol) gt 4 then
			D := Reduce(<Apol, Bpol, (J ! [Apol, Bpol])[3] + Degree(Apol)>, f);
			D := Adjust(D, f, V);
		elif Degree(Apol) eq 4 then
			D := Adjust(<Apol, Bpol, (J ! [Apol, Bpol])[3] + Degree(Apol)>, f, V);
		else
			return elt< J | Apol, Bpol>;
		end if;
		Apol := D[1];
		Bpol := D[2];
		n := D[3];
		return elt<J | Apol, Bpol, n - Degree(Apol)>;
	end if;*/
  // J = Jacobian of C : y^2 = f = Bpol^2 - Apol*Cpol
  // Apol, Bpol, Cpol polynomials of degree <= 4
  if Degree(Apol) eq 4 then
    // change divisor to get smaller degree
    // see i.e. Theorem 4.18.2 in [6]
    if Degree(Cpol) lt 4 then
      Apol := Cpol;
      Bpol *:= -1;
    else // decrease degree of Apol.												
      cofs := [Coefficient(Apol, 4), Coefficient(Bpol, 4), Coefficient(Cpol, 4)];
      flag, sqrtdisc := IsSquare(cofs[2]^2 - cofs[1]*cofs[3]);
      assert flag;
      mu := (-cofs[2] + sqrtdisc)/cofs[3];
      Apol +:= 2*mu*Bpol + mu^2*Cpol;	// A := A + (2sqrt(f_n) - 2B_n^2)/C_N * B + (f_n - 2sqrt(f_n) + B_n^2)/C_N^2
      assert Degree(Apol) lt 4;			// => A_n = A_n + (f_n - B_n^2)/C_n = 0.
      Bpol +:= mu*Cpol;
    end if;
  end if;
  // now deg(Apol) le 3
  Apol /:= LeadingCoefficient(Apol);
  Bpol := Bpol mod Apol;
  return elt<J | Apol, Bpol>;
end function;
  
		

