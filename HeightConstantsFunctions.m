/* Computes the height difference bound between the canonical and the naive height of a point on J.
The code here is designed by Prof. M. Stoll, and only slightly generalized.*/

Attach("G3HypHelp.m");
import "G3HypHelp.m": K3quartics, K3deltas, Xipolynomials, K3biquforms, K3xi2coeffs;

// We store the data with the curve

declare attributes CrvHyp:
 KummerEquations, KummerVariety, KummerDeltas, KummerXipols, KummerBQF, HeightTable;

declare verbose ReducedBasis, 2;

declare verbose FindPointsG3, 3;

import "KummerData.m": kummerD, kummerBB;
import "heights.m": normalize;
import "G3Hyp.m": MyPrec;
import "KummerArithmetic.m": MyPseudoAdd;

// Computes c_{\infty} (Section 3.4)

intrinsic HeightConstAtInfty(f::RngUPolElt : eps := 0.0001) -> FldReElt, SeqEnum
{}
    if Degree(f) eq 7 then
        partitions := [<s, {1..7} diff s> : s in Subsets({1..7}, 3)];
    else
        partitions := [<s, {1..8} diff s> : s in Subsets({1..8}, 4)];
    end if;
    // extract & print all roots of f in C.
    roots := [r[1] : r in Roots(f, ComplexField())];
    vprintf JacHypHeight, 2: " Roots of f:\n";
    if GetVerbose("JacHypHeight") ge 2 then
        Cprt<i> := ComplexField(15);
        for r in roots do printf "   %o\n", Cprt!r; end for;
        delete Cprt;
    end if;
    lcf := Abs(LeadingCoefficient(f));
    // Find a bound for the local height constant at infinity
    function step(ds)
        aseq := [0.0 : i in [1..8]];
        PC := PolynomialRing(ComplexField());
        X := PC.1;
        for pi in partitions do
            p1 := pi[1]; p2 := pi[2];
            spol := &*[X - roots[i] : i in p1];
            tpol := &*[X - roots[i] : i in p2];
            s4, s3, s2, s1 := Explode(Coefficients(spol)); s0 := 0;
            t4, t3, t2, t1, t0 := Explode(Coefficients(tpol));
            st02 := s2*t0 + s0*t2;
            st03 := s3*t0 + s0*t3;
            st04 := s4*t0 + s0*t4;
            st13 := s3*t1 + s1*t3;
            st14 := s4*t1 + s1*t4;
            st24 := s4*t2 + s2*t4;
            // find bound on absolute value of y_T, making use of the fact that delta(x) is real
            // and bounded in absolute value component-wise by ds
            cofs := [lcf*st02*ds[7], lcf*st03*ds[6], lcf*st04*ds[5],
                lcf*(st04+st13)*ds[4], lcf*st14*ds[3], lcf*st24*ds[2],
                lcf^2*(st02*st24 - st03*st14 + st04*(st04+st13))*ds[1]];
            b := Sqrt(Max([Modulus(ds[8] + e1*cofs[1] + e2*cofs[2] + e3*cofs[3] + e4*cofs[4]
                                         + e5*cofs[5] + e6*cofs[6] + e7*cofs[7])
                                        : e1,e2,e3,e4,e5,e6,e7 in [1,-1]]));
//       b := Sqrt(ds[8] + lcf*(Modulus(st02)*ds[7] + Modulus(st03)*ds[6] + Modulus(st04)*ds[5]
//                         + Modulus(st04 + st13)*ds[4] + Modulus(st14)*ds[3] + Modulus(st24)*ds[2])
//                   + lcf^2*Modulus(st02*st24 - st03*st14 + st04*(st04+st13))*ds[1]);
            res := lcf^4*&*[roots[i] - roots[j] : i in p1, j in p2];
            rr := Modulus(b/(8*res));
            // get coefficients \upsilon_j(T)
            xicof := K3xi2coeffs(spol, lcf*tpol);
            for j := 1 to 8 do
                aseq[j] +:= rr*Modulus(xicof[j]);
            end for;
        end for;
        return [Sqrt(a) : a in aseq];
    end function;
    ds := [1.0 : i in [1..8]];
    bsum := 0.0;
    n := 1;
    ds := step(ds);
    maxd := Max(ds);
    bsum +:= 4^n*Log(maxd);
    ds := [d/maxd : d in ds];
    bound := bsum/(4^n-1);
    vprintf JacHypHeight, 2: "  first bound: %o\n", ChangePrecision(bound, 6);
    repeat
        n +:= 1;
        ds := step(ds);
        maxd := Max(ds);
        bsum +:= 4^n*Log(maxd);
        ds := [d/maxd : d in ds];
        oldbound := bound;
        bound := bsum/(4^n-1);
        vprintf JacHypHeight, 2: "  new bound: %o\n", ChangePrecision(bound, 6);
        // assert bound le oldbound; // <--- Unproven, but expected to hold.
  until oldbound - bound lt eps;
  return bound;
end intrinsic;

/* This computes a height bound \beta such as in (Theorem 3.15)*/

intrinsic HeightConstantG3(J::JacHyp : eps := 0.0001) -> FldReElt, FldReElt
{If J is the Jacobian of a genus 3 curve defined over the rationals,
 of the form  y^2 = f(x)  with integral coefficients, this computes
 a real number c such that  h_K(P) le h(P) + c  for all P in J(Q),
 where h_K is the naive logarithmic height got from the Kummer surface
 and h is the canonical height on J.}
    C := Curve(J);
    require Genus(C) eq 3 and CoefficientRing(C) cmpeq Rationals():
        "HeightConstant is implemented",
        "for Jacobians of genus 3 curves over the rationals.";
    f, h := HyperellipticPolynomials(C);
    require h eq 0 and &and[ Denominator(c) eq 1 : c in Coefficients(f)]:
        "HeightConstant needs a curve of the form  y^2 = f(x), ",
        "where f has integral coefficients.";
    if assigned J`HeightConst then
        return J`HeightConst[1], J`HeightConst[2];
    end if;
    vprintf JacHypHeight, 1: "Find height constant for J =\n%o\n", J;
    hc_inf := HeightConstAtInfty(f : eps := eps); // Height constant at infinity
    vprintf JacHypHeight, 1: " Bound for height constant at infinity:\n";
    vprintf JacHypHeight, 1: "   %o\n", hc_inf;
	// Now find a bound for the finite part
	// disc is |disc(F)|: Disc(C) = 2^(4*Genus(C)) * Disc(F), see i.e. [2].
    disc := Integers()!Abs(Discriminant(C)/2^12);
    c := GCD(ChangeUniverse(Eltseq(f), Integers())); // c is the content of F.
    disc1 := ExactQuotient(64*disc, c^10); // dividing by c^10, not described in [3].
    hc_finite := Log(disc1)/3;
    vprintf JacHypHeight, 1: " Bound for finite part of height constant:\n";
    vprintf JacHypHeight, 1: "   %o\n", hc_finite;
    vprintf JacHypHeight, 1: " Result infinite + finite is\n  %o\n\n",
                                                    hc_inf + hc_finite;
    // Determine upper bound for |delta(P)|/|P|^4 at infinity
    deltas := kummerD(C);
    hc_inf_both := Max(hc_inf,
                     1/3*Log(Max([Abs(t) : t in &cat[Coefficients(d) : d in deltas]])));
    J`HeightConst := <hc_finite + hc_inf, hc_inf_both>;
    return hc_finite + hc_inf, hc_inf_both;
end intrinsic;
