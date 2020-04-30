/* Various functions regarding the height of a point.
	normalize: Given rational coordinates of a point P projectively, gives equivalent coordinates
				s.t. all coordinates are integers and share no common divisor.
	NaiveHeight: Given a curve C and point P on K, computes Naive Height of P.
	NaiveHeightG3: Given P on Jacobian(C) of C of genus 3, computes Naive Height of P.
	CanonicalHeightG3: Given P on Jacobian(C) of C of genus 3, computes canonical height of P. 

*/

Attach("G3HypHelp.m");
import "G3HypHelp.m": K3quartics, K3deltas, Xipolynomials, K3biquforms, K3xi2coeffs;

// We store the data with the curve

declare attributes CrvHyp:
 KummerEquations, KummerVariety, KummerDeltas, KummerXipols, KummerBQF, HeightTable;

declare verbose ReducedBasis, 2;

declare verbose FindPointsG3, 3;

function normalize(seq) // normalize to a sequence of integers whose gcd = 1
	i := 1;
	while i le #seq and seq[i] eq 0 do
		i +:= 1;
	end while;
	if i gt #seq then
		return seq;
	end if;
  seq := [Integers() | a*x : x in seq] where a := LCM([Denominator(x) : x in seq]);
  seq := [ExactQuotient(x,b) : x in seq] where b := GCD(seq);
  return seq;
end function;

intrinsic NaiveHeight(C::CrvHyp, P::Pt) -> FldReElt
{The naive height of the point P on the Kummer variety of C.}
  s := Eltseq(P);
  assert Universe(s) cmpeq Rationals();
  return Log(Max(normalize(s)));
end intrinsic;

intrinsic NaiveHeightG3(P:JacHypPt) -> FldReElt
{The naive height of the point P on a genus 3 hyperelliptic Jacobian.}
  return NaiveHeight(Curve(Parent(P)), ToKummerVariety(P));
end intrinsic;

intrinsic CanonicalHeightG3(P::JacHypPt : Precision := 0) -> FldReElt
{Computes the canonical height of P. The genus must be 3.}
  return CanonicalHeight(Curve(Parent(P)), ToKummerVariety(P) : Precision := Precision);
end intrinsic;
