AttachSpec("spec");
Attach("torsion3.m");

import "G3Hyp.m": normalize;

SetVerbose("FindPointsG3", 0);

R<x> := PolynomialRing(Rationals());
C := HyperellipticCurve(x^5+x^3,x^4+x^2+1);
C := SimplifiedModel(C);
J := Jacobian(C);
K := KummerVarietyG3(C);
c := Floor(HeightConstantG3(J));

tb := TorsionBound(J, 15);

q := 3;
disc := Discriminant(C);
while true do
	if Integers()!disc mod Integers()!q ne 0 and IsPrime(q) then
		p := q;
		break;
	end if;
	q +:= 2;
end while;
// Can use BadPrimes(C)

Jp := BaseChange(J, GF(p));

B := Ceiling(HeightConstantG3(J));

// print Order(J ! [x^3 + 2*x^2 + 5*x + 8, x^2 + x + 9]);

G, iso := myTwoTorsionSubgroup(J);

lst := {};
for P in G do
  Include(~lst, iso(P));
end for;
Pts := Points(Jp);
print #Pts;
i := 0;
for redPt in Pts do
  i +:= 1;
  // print i, "/", #Pts, redPt;
  lifts := FindRationalPoints(C, ToKummerVariety(redPt), B: count := 7);
  for P in lifts do
    if P in lst then
      continue redPt;
    end if;
    mult := {P};
    P2 := P;
    while true do // what's going on here?
      P2 +:= P;
      Include(~mult, P2);
      if P2 eq J ! 0 then
        lst := lst join mult;
        break;
      end if;
    end while;
  end for;
  if #lst eq tb then
    break;
  end if;
end for;


for pt in lst do
	print pt;
end for;



/*
pts := {};
for elt in box do
  if elt eq box ! [0,0,0,0,0,0,0,0] then
    continue elt;
  end if;
  P := ChangeUniverse(Eltseq(elt), Integers());
  if IsPointOnKummer(C, P) and P notin pts then
    P := K ! P;
    P1 := KummerOrigin(C);
    P2 := P;
    order := 1;
    lst := {P};
    while NaiveHeight(C, P2) lt c do
	  order +:= 1;
	  Q := P2;
      P2 := PseudoAdd(C, P2, P, P1);
      P1 := Q;
      lst := Include(lst, P2);
      if P2 eq KummerOrigin(C) then
        pts := pts join lst;
        print pts;
        if #pts eq tb then
          break elt;
        end if;
        break;
      end if;
    end while;
  end if;
end for; 

for pt in pts do
  LiftToJacobian(C, pt);
  print pt;
end for;
*/


