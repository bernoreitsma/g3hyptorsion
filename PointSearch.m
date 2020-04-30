/* Functions and an intrinsic ultimately designed to find rational points on Jacobian(C) that, when
mapped to K and reduced modulo p result in P on K over F_p.
	projLattice: Takes L and primitive vector v, gives L/<v> and abstract map from L1 to L.
	collect: Given lattice L, height H and function "test", returns the union of the image of
				test of all points on L with height <= H.
	FindRationalPoints: Given curve C, P on the Kummer Variety associated with C, reduced mod p,
						computes on all rational points on J that have a point on K that reduces mod p
						to P.
*/

Attach("G3HypHelp.m");
import "G3HypHelp.m": K3quartics, K3deltas, Xipolynomials, K3biquforms, K3xi2coeffs;

// We store the data with the curve

declare attributes CrvHyp:
 KummerEquations, KummerVariety, KummerDeltas, KummerXipols, KummerBQF, HeightTable;

declare verbose ReducedBasis, 2;

declare verbose FindPointsG3, 3;

import "heights.m": normalize;



function projLattice(L, v)
  // L: lattice, v: primitive vector in L
  // returns the projected lattice L/<v> and a map that lifts to L
  qL, qmap := quo<L | v>;
  assert IsFree(qL); // qL is an abelian group
  bas := [qL.i @@ qmap : i in [1..Ngens(qL)]];
  // compute Gram matrix of quotient lattice
  baspr := [b - (b,v)/(v,v)*v : b in bas];
  L1 := LatticeWithGram(Matrix([[(b1,b2) : b2 in baspr] : b1 in baspr]));
  liftmap := map<L1 -> L | v1 :-> &+[v1[i]*bas[i] : i in [1..#bas]]>;
  return L1, liftmap;
end function;

function collect(L, H, test : primitive := true, factor := 100, count := 3)
  // L: lattice, H: height bound,
  // test: function that applied to lattice point returns an indexed set
  // returns the union of test applied to all primitive lattice points
  // of norm at most H
  result := {@ @};
  dim := Dimension(L);
  svheight := Ceiling(H^(1/dim)); // expected norm of shortest vector
//   vprintf FindPointsG3, 3: " successive minima: %o\n", SuccessiveMinima(L);
  vprintf FindPointsG3, 3: " finding shortest vectors...\n";
  sv := ShortestVectors(L)[1];
  if (sv,sv) lt factor*svheight and dim gt 1 and count gt 0 then
    vprintf FindPointsG3, 2: "  projecting lattice...\n";
    // fairly short shortest vector
    new := test(Eltseq(sv));
    if not IsEmpty(new) then
      vprintf FindPointsG3, 3: "   Found points %o\n", new;
    end if;
    result join:= new;
    // now search on projected lattice
    L1, lift := projLattice(L, sv);
    function newtest(v)
      v1 := lift(v);
      res := {@ @};
      pol := Polynomial(Rationals(), [(v1,v1) - H, 2*(v1,sv), (sv,sv)]);
      rts := [r[1] : r in Roots(pol, RealField())];
      if #rts eq 2 then
        for n := Ceiling(rts[1]) to Floor(rts[2]) do
          res join:= test(v1 + n*sv);
        end for;
      elif #rts eq 1 then	// treated as particular case, does the same thing
        flag, sqrt := IsSquare(1/LeadingCoefficient(pol)*pol);
        assert flag;	// this is really expected to happen in this context...
        if Coefficient(sqrt, 0) in Integers() then
          new := test(v1 - (Integers()!Coefficient(sqrt, 0))*sv);
          if not IsEmpty(new) then
            vprintf FindPointsG3, 3: "   Found points %o\n", new;
          end if;
          res join:= new;
        end if;
      end if;
      return res;
    end function;
    result join:= collect(L1, H, newtest : primitive := false, factor := factor, count := count-1);
    return result;
  else
    // lattice is not too skew
    if count eq 0 then
      return result;
    end if;
    vprintf FindPointsG3, 2: "  running ShortVectorsProcess...\n";
    svproc := ShortVectorsProcess(L, H);
    while not IsEmpty(svproc) do
      v := NextVector(svproc);
      if not primitive or GCD(ChangeUniverse(Eltseq(v), Integers())) eq 1 then
        new := test(v);
        if not IsEmpty(new) then
          vprintf FindPointsG3, 3: "   Found points %o\n", new;
        end if;
        result join:= new;
      end if;
    end while;
  end if;
  return result;
end function;

intrinsic FindRationalPoints(C::CrvHyp, P::Pt, H::RngIntElt : twist := 1, factor := 100, count := 3) -> SetIndx
{Find all rational points on the Jacobian of the Kummer Variety K of multiplicative naive height
at most H whose image on K reduces mod the prime p to P.}
  Ct := twist eq 1 select C else QuadraticTwist(C, twist);
  K := KummerVarietyG3(C);
  eqns := DefiningEquations(K);
  F := Universe(Eltseq(P));
  p := Characteristic(F);
  assert F eq GF(p);
  eqnsF := ChangeUniverse(eqns, PolynomialRing(F, 8));
  vprintf FindPointsG3, 2: "point: %o\n", P;
  vprintf FindPointsG3, 1: "Setting up Jacobian matrix...\n";
  Pint := ChangeUniverse(Eltseq(P), Integers());
  jac := JacobianMatrix(eqnsF);
  vprintf FindPointsG3, 1: " and evaluating it at P...\n";
  jac := Matrix(F, [[Evaluate(jac[i,j], Eltseq(P)) : j in [1..NumberOfColumns(jac)]]
                      : i in [1..NumberOfRows(jac)]]);
  rank := Rank(jac);
  vprintf FindPointsG3, 1: "rank is %o\n", rank;
  if rank lt 4 then
    printf "point is singular. Abort.\n";
//     vprintf FindPointsG3, 1: "point is singular. Abort.\n";
//     i := 1;
//     while P[i] ne 1 do i +:= 1; end while;
//     assert i le 8;
//     P8<[x]> := Universe(eqns);
//     evseq1 := [Pint[j] + p*(j lt i select x[j] else j gt i select x[j-1] else 0)
//                : j in [1..8]];
//     quad := 1/p*Evaluate(eqns[1], evseq1);
//     quadF := Universe(eqnsF)!quad;
//     assert TotalDegree(quadF) eq 1;
//     k := 1;
//     while MonomialCoefficient(quadF, Parent(quadF).k) eq 0 do k +:= 1; end while;
//     // solve for x[k]
//     solxk := &+[j eq k select 0
//                        else Integers()!MonomialCoefficient(quadF, Parent(quadF).j)*x[j]
//                  : j in [1..7]];
//     evseq2 := [j eq k select p*x[k] - solxk else x[j] : j in [1..8]];
//     evseq := [Evaluate(e, evseq2) : e in evseq1];
//     eqns1 := [Evaluate(e, evseq) : e in eqns];
//     eqns1 := [1/p^Min([Valuation(c, p) : c in Coefficients(e)])*e : e in eqns1];
//     PF7 := PolynomialRing(F, 7);
//     toPF7 := hom<Universe(eqnsF) -> PF7 | [PF7.i : i in [1..7]]  cat [0]>;
//     eqns1F := [toPF7(Universe(eqnsF)!e) : e in eqns1];
//     vprintf FindPointsG3, 1: "computing points on blow-up...\n";
//     var := Variety(ideal<PF7 | eqns1F>);
//     vprintf FindPointsG3, 1: " ...%o points\n", #var;
    result := {@ Jacobian(Ct) | @};
//     for pt in var do
//       P := [pt[i] : i in [1..7]];
//       jac := JacobianMatrix(eqns1F);
//       jac := Matrix(F, [[Evaluate(jac[i,j], P) : j in [1..NumberOfColumns(jac)]]
//                          : i in [1..NumberOfRows(jac)]]);
//       rank := Rank(jac);
//       if rank lt 4 then
//         vprintf FindPointsG3, 1: "new rank is %o -- too small. Skip.\n", rank;
//       else
//         Pint := ChangeUniverse(P, Integers());
//
//       end if;
//     end for;
    return result;
  end if;
  as := -Vector(F, [F| ExactQuotient(Evaluate(eqn, Pint), p) : eqn in eqns]);
  vprintf FindPointsG3, 1: "solving linear system...\n";
  sol, ker := Solution(Transpose(jac), as);
  vprintf FindPointsG3, 1: "...done\n";
  sol := ChangeRing(sol, Integers());
  Pint := Vector(Pint) + p*sol;
  vprintf FindPointsG3, 1: "setting up lattice...\n";
	L := Lattice(Matrix([Eltseq(Pint)]
                       cat [Eltseq(p*ChangeRing(b, Integers())) : b in Basis(ker)]
                       cat [[i eq j select p^2 else 0 : j in [1..8]] : i in [1..8]]));
	/*L := Lattice(Matrix([Eltseq(Pint)] 
								cat [[i eq j select p else 0 : j in [1..8]] : i in [1..8]]));  */       
  function test(v)
    if GCD(ChangeUniverse(Eltseq(v), Integers())) eq 1
        and forall{e : e in eqns | Evaluate(e, Eltseq(v)) eq 0} then
      return LiftToJacobian(C, K!Eltseq(v) : twist := twist);
    else
      return {@ Jacobian(Ct) | @};
    end if;
  end function;
  vprintf FindPointsG3, 1: "collecting points...\n";
  result := collect(L, 8*H^2, test : factor := factor, count := count);
  vprintf FindPointsG3, 1: "... found %o points on J\n", #result;
  return result;
end intrinsic;

intrinsic IsPointOnKummer(C::CrvHyp, s::SeqEnum: Ambient := "") -> boolelt
{Checks if point represented by a sequence is actually on the Kummer Variety of C.}
  K := KummerVarietyG3(C: Ambient := Ambient);
  for pol in Equations(K) do
		if Evaluate(pol, s) ne 0 then
	  	return false;
		end if;
  end for;
  return true;
end intrinsic;


