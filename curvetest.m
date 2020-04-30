AttachSpec("spec");
Attach("torsion3.m");
Attach("transformations.m");
import "transformations.m": KummerTransformation;

SetSeed(2594609949);

S<x> := PolynomialRing(Rationals());
C := HyperellipticCurve(x^8-4*x^7+8*x^6-9*x^5+7*x^4-4*x^2+5*x-2, x^4+x^3+1);
C := SimplifiedModel(MinimalWeierstrassModel(C));
G := myTorsionSubgroup(Jacobian(C));

// -x^7-4*x^6-3*x^5+2*x^4+x^3-x^2,x^3+1
