/* The arithmetic functions on the Kummer Variety.
	KummerOrigin: Computes K ! 0.
	Double: Given P, computes 2*P
	KummerXI: Computes equations used in PseudoAdd, see [3], section 7
	PseudoAdd: Given P, Q, P - Q, computes P + Q.
	Multiple: Given P, n, computes n*P
	PseudoAddMultiple: Given P, Q, P - Q, n, computes P + n*Q.
*/

Attach("G3HypHelp.m");
import "G3HypHelp.m": K3quartics, K3deltas, Xipolynomials, K3biquforms, K3xi2coeffs;

// We store the data with the curve

declare attributes CrvHyp:
 KummerEquations, KummerVariety, KummerDeltas, KummerXipols, KummerBQF, HeightTable;
 
import "KummerData": kummerD, kummerBB;
 
intrinsic KummerOrigin(C::CrvHyp : Ambient := "") -> Pt
{Return the origin on the Kummer variety of the curve C.}
    return KummerVarietyG3(C : Ambient := Ambient)![0,0,0,0,0,0,0,1];
end intrinsic;


/* ---------------------------------------------------------------------------*/
// Note: I might need to rewrite the code in order to take K as argument instead
// of C in the arithmetic operations.

// Attributes dependent on Ambient should be changed into an a "function" type that
// retrieves Ambient and returns/saves the attribute specific to that Ambient.
/*----------------------------------------------------------------------------*/

/* Doubling (Section 2.7.2) */

intrinsic Double(C::CrvHyp, P::Pt: Ambient := "") -> Pt
{Double the point P on the Kummer variety of C.}
    // KummerDeltas are the explicit formulas for delta_i, the doubling function
    // as introduced in [3], section 7.
  
    if assigned C`KummerDeltas and Ambient cmpeq "" then
        deltas := C`KummerDeltas;
        R := Universe(deltas);
    else // if the attribute KummerDeltas have to be computed.
        // standard condition checks on the curve.
        require Genus(C) eq 3: "The curve must be of genus 3.";
        f, h := HyperellipticPolynomials(C);
        require h eq 0: "The curve must have the form y^2 = f(x).";

        // eltseq of coefs of f in Ambient and its polynomial ring
        fs := Ambient cmpeq ""
		    select Coefficients(f)
		    else Coefficients(PolynomialRing(CoordinateRing(Ambient)) ! f);
        fs cat:= [0 : i in [#fs+1..9]];
        R :=   PolynomialRing(Universe(fs), 8);
           
        // Creation of/assigning Kummer Deltas.       
        deltas := K3deltas(fs : Ring := R);
        if Ambient cmpeq "" or BaseRing(Ambient) cmpeq BaseRing(C) then
            C`KummerDeltas := deltas;
        end if;
    end if;
  
    // Compute 2*P.
    P2 := [Evaluate(d, s) : d in deltas] where s := Eltseq(P);
    K := KummerVarietyG3(C : Ambient := Ambient);
    return K!P2;
end intrinsic;

import "heights.m":normalize;

// An explanation for KummerXi-polynomials can be found at the end of
// section 7 of [3].

intrinsic KummerXi(C::CrvHyp, P::Pt: Ambient := "") -> RngElt
{Computes the value of Xi on the given coordinates of P.}
    if assigned C`KummerXipols and Ambient cmpeq "" then
        Xipols := C`KummerXipols;
    else // if Xipols still have to be computed
        // check standard curve conditions
        require Genus(C) eq 3: "The curve must be of genus 3.";
        f, h := HyperellipticPolynomials(C);
        require h eq 0: "The curve must have the form y^2 = f(x).";
    
        // compute coefficients of f and its polynomial ring.
        fs := Ambient cmpeq ""
            select Coefficients(f)
            else Coefficients(PolynomialRing(CoordinateRing(Ambient)) ! f);
        fs cat:= [0 : i in [#fs+1..9]];
        R :=   PolynomialRing(Universe(fs), 8);
           
        // compute, assign XiPols
        Xipols := Xipolynomials(fs : Ring := R);
        if Ambient cmpeq "" or BaseRing(Ambient) cmpeq BaseRing(C) then
            C`KummerXipols := Xipols;
        end if;
    end if;	// note: changed ne 0 to IsUnit() here.
    i := 1; while not IsUnit(P[i]) do i +:= 1; end while;
    return Parent(P[i]) ! Evaluate(Xipols[i], Eltseq(P)) / P[i];
end intrinsic;

/* Pseudo-Addition (Section 2.7.2) */

intrinsic PseudoAdd(C::CrvHyp, P1::Pt, P2::Pt, P3::Pt: Ambient := "") -> Pt
{Given the images on the Kummer variety of C of points P, Q, P-Q on the
Jacobian of C, returns the image of P+Q.}
    // make eltseq's that are compatible to evaluation on Biquforms.
    L12 := Eltseq(P1) cat Eltseq(P2);
    L3 := Eltseq(P3);
    // i := K`SelectCoordinate(L3);
    i := 1; while not IsUnit(L3[i]) do i +:= 1; end while;
    if assigned C`KummerBQF then
        BB := C`KummerBQF;
    else
        // basic curve conditions
        require Genus(C) eq 3: "The curve must be of genus 3.";
        f, h := HyperellipticPolynomials(C);
        require h eq 0: "The curve must have the form y^2 = f(x).";
        fs := Coefficients(f);  
        fs cat:= [0 : i in [#fs+1..9]];
        BB := K3biquforms(fs);
        C`KummerBQF := BB;
    end if;
/*	if not Ambient cmpeq "" then
		BB := ChangeRing(BB, PolynomialRing(CoordinateRing(Ambient)));
	end if;*/
    // account for the last term if BQF, see [3], eqn. 8.1
    Xi := KummerXi(C, P1: Ambient := Ambient)*KummerXi(C, P2: Ambient := Ambient);
    signs := [1,-1,1,-1,-1,1,-1,1]; // anti-diagonal of S in [3].
    c1 := 2*L3[i]; c2 := Evaluate(BB[i,i], L12);
    L := [ c1*(Evaluate(BB[i,j], L12) + (i+j eq 9 select signs[i]*Xi else 0))
            - L3[j]*c2 : j in [1..8] ];
    // Check if point really is on K here, since third argument might
    // not be image of P-Q.
    assert IsPointOnKummer(C, L: Ambient := Ambient);
    return KummerVarietyG3(C : Ambient := Ambient)!L;
end intrinsic;

/* 
For R, computes [[n]]R, see (Section 2.7.2)
*/

intrinsic Multiple(C::CrvHyp, n::RngIntElt, P::Pt: Ambient := "") -> Pt
{The n-th multiple of P on the Kummer variety of the curve C.}
    if n eq 0 then return KummerOrigin(C); end if;
    m := Abs(n);
    Px := KummerOrigin(C : Ambient := Ambient); Py := P; Pz := P;
    // invariants: Px = ax*P, Py = ay*P, Pz = az*P with
    //  ax + ay = az  and  ax + m*az = n .
    while true do
        if IsOdd(m) then
            Px := PseudoAdd(C, Px, Pz, Py: Ambient := Ambient);
        else
            Py := PseudoAdd(C, Py, Pz, Px: Ambient := Ambient);
        end if;
        m div:= 2;
        if m eq 0 then return Px; end if;
        Pz := Double(C, Pz: Ambient := Ambient);
    end while;
end intrinsic;

/* PseudoAddMultiple is very similar to Multiple, we simply start with
P and Q already established, and add Q whenever we encounter a '1' in the
binary expansion of n, and add to the difference otherwise. Interpret
P1 as "sum so far iterating through the binary expansion of n."
P2 as "2^i * Q"
P3 as "difference between P1 and 2^k * Q"
*/

intrinsic PseudoAddMultiple(C::CrvHyp, P1::Pt, P2::Pt, P3::Pt, n::RngIntElt: Ambient := "") -> Pt
{Given the images on the Kummer variety of the curve C of points P, Q, P-Q on the
Jacobian, returns the image of P+n*Q.}
    if n lt 0 then
        P3 := PseudoAdd(C, P1, P2, P3: Ambient := Ambient); n := -n;
    end if;
    while true do
        if IsOdd(n) then
            P1 := PseudoAdd(C, P1, P2, P3: Ambient := Ambient);
        else
            P3 := PseudoAdd(C, P3, P2, P1: Ambient := Ambient);
        end if;
        n div:= 2;
        if n eq 0 then return P1; end if;
        P2 := Double(C, P2: Ambient := Ambient);
    end while;
end intrinsic;

// The following does the "pseudo-addition" on a Kummer variety over a p-adic field
// directly on the coordinate sequences.
// This avoids error messages and should be more efficient, since no algebraic-geometric
// objects need to be constructed.
function MyPseudoAdd(C, P1, P2, P3)
    // C = genus 3 hyp. curve (over Q), P1, P2, P3 coordinate sequences in a p-adic field.
    // Returns normalized coordinates for P1+P2 (assuming P3 = P1-P2)
    // and the relative precision of the result.
    // (Compare $MAGMA_ROOT/package/Geometry/CrvG2/kummer.m)
    BB := kummerBB(C);
    Xi := KummerXi(C, P1)*KummerXi(C, P2);
    P12 := P1 cat P2;
    v, i := Min([Valuation(s) : s in P3]);
    signs := [1,-1,1,-1,-1,1,-1,1];
    c1 := 2*P3[i]; c2 := Evaluate(BB[i,i], P12);
    L := [ c1*(Evaluate(BB[i,j], P12) + (i+j eq 9 select signs[i]*Xi else 0))
        - P3[j]*c2 : j in [1..8] ];
    v := Min([Valuation(s) : s in L]);
    sh := UniformizingElement(Universe(P1))^-v;
    return [s * sh : s in L], Min([AbsolutePrecision(s) - v : s in L]);
end function;
