/* Functions computing the height pairing of a point*/

Attach("G3HypHelp.m");
import "G3HypHelp.m": K3quartics, K3deltas, Xipolynomials, K3biquforms, K3xi2coeffs;

// We store the data with the curve

declare attributes CrvHyp:
 KummerEquations, KummerVariety, KummerDeltas, KummerXipols, KummerBQF, HeightTable;

declare verbose ReducedBasis, 2;

declare verbose FindPointsG3, 3;

intrinsic HeightPairingG3(P::JacHypPt, Q::JacHypPt : Precision := 0) -> FldReElt
{Computes the canonical height pairing of P and Q (on the same Jacobian),
 defined by  <P,Q> := (h(P+Q) - h(P) - h(Q))/2.
 The genus must be 3, and the base field must be the rationals. }
  require Parent(P) eq Parent(Q): "Points must be on the same Jacobian.";
  return (CanonicalHeightG3(P+Q : Precision := Precision)
           - CanonicalHeightG3(P : Precision := Precision)
           - CanonicalHeightG3(Q : Precision := Precision))/2;
end intrinsic;

intrinsic HeightPairingMatrixG3(S::[JacHypPt] : Precision := 0) -> AlgMat
{Given a sequence of points P_i on a Jacobian (of a curve of genus 3
 over the rationals), this returns the matrix  (<P_i, P_j>), where
 < , > is the canonical height pairing. }
  n := #S;
  hs1 := [ CanonicalHeightG3(P : Precision := Precision) : P in S ];
  hs2 := [ [ (CanonicalHeightG3(S[i]+S[j] : Precision := Precision)
                - hs1[i] - hs1[j])/2: i in [1..j-1] ]
           : j in [2..n] ];
  mat := [ (i eq j) select hs1[i] else
           (i lt j) select hs2[j-1,i] else hs2[i-1,j] : i,j in [1..n] ];
  // changed that to not set the coefficient field... MS 2004-10
  // return MatrixRing(RealField(), n)!mat;
  return Matrix(n, mat);
end intrinsic;
