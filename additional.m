AttachSpec("spec");
Attach("torsion3.m");
Attach("transformations.m");
load "abs_simple.m";
_<x> := PolynomialRing(Rationals());

X1 := HyperellipticCurve(x*(x-1)*(x-2)*(x-3)*(x-4)*(x^2+x+1));
X2 := HyperellipticCurve(x*(x-1)*(x-2)*(x-3)*(x+1)*(x+2)*(x+3));
X3 := HyperellipticCurve(x^7 - 8*x^6 - 19*x^5 + 235*x^4 - 130*x^3 - 875*x^2 - 500*x);
X4 := HyperellipticCurve(x^7 - 15*x^6 + 87*x^5 - 244*x^4 + 335*x^3 - 191*x^2 + 9*x + 18);

"X1", X1;
invs := InvariantFactors(myTorsionSubgroup(Jacobian(X1)));
"invariant factors", invs; // [2,2,2,2,2]
"geometrically simple?",  HasAbsolutelyIrreducibleJacobian(X1, 50);

"X2", X2;
invs := InvariantFactors(myTorsionSubgroup(Jacobian(X2)));
"invariant factors", invs; // [2,2,2,2,2,2]
"geometrically simple?",  HasAbsolutelyIrreducibleJacobian(X2, 50);

"X3", X3;
invs := InvariantFactors(myTorsionSubgroup(Jacobian(X3)));
"invariant factors", invs; // [2,2,2,2,4]
"geometrically simple?",  HasAbsolutelyIrreducibleJacobian(X3, 50);

"X4", X4;
invs := InvariantFactors(myTorsionSubgroup(Jacobian(X4)));
"invariant factors", invs; // [2,2,2,6]
"geometrically simple?",  HasAbsolutelyIrreducibleJacobian(X4, 50);

