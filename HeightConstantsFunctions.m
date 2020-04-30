/* Computes various height constants that work as bounds that are used to end the torsion algorithm.
	HeightConstAtInfty: Computes \gamma_\infty, is only implemented for degree 7.
	HeightConstantG3: Computes (logarithmic) Height Bound beta s.t. H(P) = \hat{H}(P) + \beta.
	CanonicalHeight: Computes the canonical height \hat{H}(P) of P. (Why do we need this?)
*/

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


// this only works for degree 7, degree 8 is a hard case.
intrinsic HeightConstAtInfty(f::RngUPolElt : eps := 0.0001) -> FldReElt, SeqEnum
{}
    // make partitions of {1..Degree(f)}, degree 8 partitions implemented 
    // by myself, but this is still not finished.
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

/* This computes the constant obtained in Cor 10.3 of [3].*/

intrinsic HeightConstantG3(J::JacHyp) -> FldReElt, FldReElt
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
  // assert Degree(f) eq 7;
  vprintf JacHypHeight, 1: "Find height constant for J =\n%o\n", J;
  hc_inf := HeightConstAtInfty(f); // Height constant at infinity
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

// the canonical height is not used as we search for rational torsion points (which have can. hght 0)

/*
intrinsic CanonicalHeight(C::CrvHyp, P::Pt : Precision := 0, Check := true) -> FldReElt
{Computes the canonical height of P on the Kummer variety of C.}
  // Some checks
  R := BaseRing(C);
  TR := Type(R);
  require TR eq FldRat:
          "CanonicalHeight for genus 3 is only implemented for the rationals as base field.";
  f := HyperellipticPolynomials(C);
  require forall{c : c in Coefficients(f) | Denominator(c) eq 1}:
          "Defining polynomial of the curve must have integral coefficients.";
  if not assigned C`HeightTable then
    C`HeightTable := AssociativeArray(Parent(P));
  end if;
  if Precision le 0 then
    Precision := MyPrec(RealField()); // use default precision
  end if;
  if IsDefined(C`HeightTable, P) then
    ht, prec := Explode(C`HeightTable[P]);
    if prec ge Precision then
      return ChangePrecision(ht, Precision);
    end if;
  end if;
  P1s := normalize(Eltseq(P));
  vprintf JacHypHeight: "CanonicalHeight: P = %o\n", P1s;
  K := KummerVarietyG3(C); // the Kummer variety on which P lies
  D := kummerD(C);   // the sequence consisting of the eight duplication polynomials
  Rs := RealField(Precision+5); // work with slightly higher precision
  if P eq KummerOrigin(C) then
    vprintf JacHypHeight: " P = 0, so height is zero.\n";
    return ChangePrecision(Rs!0, Precision);
  end if;
  // Find the mu_p(P) for the bad primes
  P2s := [ Integers() | Evaluate(D[j], P1s) : j in [1..8]]; // double of P
  g2 := GCD(P2s);
  P2s := [ExactQuotient(a, g2) : a in P2s];
  P4s := [Integers() | Evaluate(d, P2s) : d in D]; // twice double of P
  g4 := GCD(P4s);  // g2 and g4 contain exactly the bad primes for P
  bad := Set(PrimeDivisors(g2)) join Set(PrimeDivisors(g4));
  vprintf JacHypHeight: " Bad primes: %o\n", bad;
  // For each bad prime,
  // compute multiples m*P over Q_p until epsilon_p(m*P) = 0
  // and m*P is on the component of the origin.
  sum := 0; // this is used to accumulate the finite contribution of the correction
  safety := 5; // minimal relative p-adic precision during the computation
  for p in bad do
    function normp(seq)
      i := 0; repeat i +:= 1; until seq[i] ne 0;
      return [s/seq[i] : s in seq];
    end function;
    vprintf JacHypHeight, 2: "  computing contribution at p = %o...\n", p;
    fmodp := PolynomialRing(GF(p))!f;
    issq := fmodp ne 0 and IsSquare(fmodp);
    // default p-adic precision used is twice the following
    precp := Valuation(Discriminant(C), p) + (p eq 2 select 20 else 2);
    flag := false; // flag will be set if computation with given precision was successful
    Fp := GF(p);
    Dp := ChangeUniverse(D, PolynomialRing(Fp, 8)); // used for checking epsilon = 0
    repeat
      precp *:= 2; // double p-adic precision after each unsuccessful attempt
      vprintf JacHypHeight, 2: "    current %o-adic precision is %o\n", p, precp;
      // table will be [0, eps_p(P), eps_p(2*P), ..., eps_p((n-1)*P]
      // where eps_p(n*P) = 0 with n*P on component of origin and n is minimal with this property
      v := Valuation(g2, p);
      table := [0, v];
      Qp := pAdicField(p, precp);
      m := 1;
      Pp := ChangeUniverse(Eltseq(P), Qp);    // work with coordinate sequences in Qp
      mP := Pp;                               // m*P
      mP1 := [Qp | 0, 0, 0, 0, 0, 0, 0, 1];   // (m-1)*P
      mP2 := [Qp | s*p^-v : s in P2s];        // 2*m*P
      mP3, pr := MyPseudoAdd(C, mP2, Pp, Pp); // (2*m+1)*P
      if pr le safety then continue; end if;  // restart with higher precision
      repeat
        m +:= 1;
        Ptemp, pr := MyPseudoAdd(C, mP, Pp, mP1); // compute (m+1)*P
        if pr le safety then break; end if; // restart with higher precision
        mP1 := mP;                                  // new (m-1)*P
        mP := Ptemp;                                // new m*P
        P2ms := [Evaluate(D[j], mP) : j in [1..8]]; // double of m*P
        v := Min([Valuation(s) : s in P2ms]);       // this is eps_p(m*P)
        pr := Min([AbsolutePrecision(s) : s in P2ms]);
        if pr-v le safety then break; end if; // restart with higher precision
        mP2 := [a*p^-v : a in P2ms];             // normalize mP2
        mP3, pr := MyPseudoAdd(C, mP2, Pp, mP3); // new (2*m+1)*P
        if pr le safety then break; end if; // restart with higher precision
        if v eq 0 then
          vprintf JacHypHeight, 2: "    %o*P has epsilon_p = 0\n", m;
          if issq then
            // need to check if point is on irred. component of origin
            if exists{d : d in Dp | Evaluate(d, seq) ne 0}
                where seq := ChangeUniverse(mP2, Fp) then
              vprintf JacHypHeight, 2: "         and is on component of origin\n";
              if Check then
                // check that mu really is zero
                step := func<seq | normp([Evaluate(d, seq) : d in Dp])>;
                s1 := ChangeUniverse(mP2, Fp); s2 := step(s1);
                repeat s1 := step(s1); s2 := step(step(s2)); until s1 eq s2;
              end if;
              flag := true;
              break;
            else
              vprintf JacHypHeight, 2: "         but is not on component of origin\n";
            end if;
          else
            // table is complete (we can only get here when m <= 3)
            if Check then
              // check that mu really is zero
              step := func<seq | normp([Evaluate(d, seq) : d in Dp])>;
              s1 := ChangeUniverse(mP2, Fp); s2 := step(s1);
              repeat s1 := step(s1); s2 := step(step(s2)); until s1 eq s2;
            end if;
            flag := true;
            break;
          end if;
        end if;
        // Check if eps_p(2*m*P) = 0 or eps_p((2*m+1)*P) = 0
        // by computing delta(..*P) mod p.
        // If so (and the relevant multiple of P is on the component of the origin),
        // we can complete table by symmetry.
        if exists{d : d in Dp | Evaluate(d, seq) ne 0}
             where seq := ChangeUniverse(mP2, Fp) then
          vprintf JacHypHeight, 2:
                  "    %o*P has epsilon_p = 0 (found at m = %o)\n", 2*m, m;
          if issq then
            seq2 := [Evaluate(d, seq) : d in Dp] where seq := ChangeUniverse(mP2, Fp);
            if exists{d : d in Dp | Evaluate(d, seq2) ne 0} then
              vprintf JacHypHeight, 2: "         and is on component of origin\n";
              table := table cat [v] cat table[m..2 by -1];
              if Check then
                // check that mu really is zero
                step := func<seq | normp([Evaluate(d, seq) : d in Dp])>;
                s1 := ChangeUniverse(mP2, Fp); s2 := step(s1);
                repeat s1 := step(s1); s2 := step(step(s2)); until s1 eq s2;
              end if;
              flag := true;
              break;
            else
              vprintf JacHypHeight, 2: "         but is not on component of origin\n";
            end if;
          else
            table := table cat [v] cat table[m..2 by -1];
            if Check then
              // check that mu really is zero
              step := func<seq | normp([Evaluate(d, seq) : d in Dp])>;
              s1 := ChangeUniverse(mP2, Fp); s2 := step(s1);
              repeat s1 := step(s1); s2 := step(step(s2)); until s1 eq s2;
            end if;
            flag := true;
            break;
          end if;
        end if;
        if exists{d : d in Dp | Evaluate(d, seq) ne 0}
             where seq := ChangeUniverse(mP3, Fp) then
          vprintf JacHypHeight, 2:
                  "    %o*P has epsilon_p = 0 (found at m = %o)\n", 2*m+1, m;
          if issq then
            seq2 := [Evaluate(d, seq) : d in Dp] where seq := ChangeUniverse(mP3, Fp);
            if exists{d : d in Dp | Evaluate(d, seq2) ne 0} then
              vprintf JacHypHeight, 2: "         and is on component of origin\n";
              table := table cat [v, v] cat table[m..2 by -1];
              if Check then
                // check that mu really is zero
                step := func<seq | normp([Evaluate(d, seq) : d in Dp])>;
                s1 := ChangeUniverse(mP3, Fp); s2 := step(s1);
                repeat s1 := step(s1); s2 := step(step(s2)); until s1 eq s2;
              end if;
              flag := true;
              break;
            else
              vprintf JacHypHeight, 2: "         but is not on component of origin\n";
            end if;
          else
            table := table cat [v, v] cat table[m..2 by -1];
            if Check then
              // check that mu really is zero
              step := func<seq | normp([Evaluate(d, seq) : d in Dp])>;
              s1 := ChangeUniverse(mP3, Fp); s2 := step(s1);
              repeat s1 := step(s1); s2 := step(step(s2)); until s1 eq s2;
            end if;
            flag := true;
            break;
          end if;
        end if;
        // Otherwise we extend table.
        Append(~table, v);
      until flag;
    until flag;
    vprintf JacHypHeight, 2: "  p = %o: table is %o\n", p, table;
    // compute contribution and add it to sum
    sum_p := 0;
    m_p := #table;
    r := Valuation(m_p, 2); // length of pre-period
    for n := 0 to r-1 do
      sum_p +:= table[1 + (2^n mod m_p)]/4^(n+1);
    end for;
    // now find periodic part
    n2_start := 2^r mod m_p;
    n2 := n2_start;
    c := 0;
    sum1 := 0;
    repeat
      sum1 +:= table[1 + (n2 mod m_p)]/4^c;
      c +:= 1;
      n2 := (2*n2) mod m_p;
    until n2 eq n2_start;
    // now c is the length of the period (= multiplicative order of 2 mod m_p/2^r)
    sum_p +:= 4^(-r-1)/(1 - 4^(-c))*sum1;
    vprintf JacHypHeight: "  p = %o: contribution is %o*log(%o).\n", p, -sum_p, p;
    sum -:= sum_p*Log(Rs!p);
  end for;

  // compute infinite part
  prec := Precision;
  delta := Rs!1/10^Precision;
  Rs0 := Rs;
//   eqn := DefiningPolynomial(K);
  // Determine how many iterations are necessary
  _, hc_inf := HeightConstantG3(Jacobian(C));
  bound := Ceiling(((Precision+5)*Log(10) + Log(hc_inf))/Log(4));
  vprintf JacHypHeight, 2: " Current precision = %o decimal digits\n", Precision;
  vprintf JacHypHeight, 2: " Bound for mu_infty = %o\n", hc_inf;
  vprintf JacHypHeight, 2:
          "  ==> need %o iterations for infinite part.\n", bound;
  repeat
    flag := true;
    one := Rs0!1;
    Pol := PolynomialRing(Rs0);
    x := Pol.1;
    // Convert into (floating-point!) real numbers
    s := [one*t : t in P1s];
    // Normalize such that the sup-norm is 1
    norm := Max([Abs(t) : t in s]);
    for j := 1 to 8 do s[j] /:= norm; end for;
    // The following gives a slight speed improvement
    // but is bad for numerical stability! - MS
//       D := ChangeUniverse(D, ChangeRing(Parent(D[1]), Rs0));
//       D := [one*d : d in D];
    // The height (of P) is the naive height plus mu_infty(P) plus the finite
    // part,
    // where mu_infty(Q) = sum_{n ge 0} eps_infty(2^n*Q)/4^(n+1)
    // where eps_infty(Q) is the local height constant at infinity at Q.
    ht := Log(norm);
    vprintf JacHypHeight: " Naive height = %o\n",ht;
    sum_inf := 0;
    pow4 := one;
    for n := 1 to bound do
      // double the point
      s := [Evaluate(D[j], s) : j in [1..8]];
      vprintf JacHypHeight, 4: "  precision of s: %o\n", [MyPrec(a) : a in s];
      // Normalize such that the sup-norm is 1
      norm := Max([Abs(t) : t in s]);
      // A safety measure:
      if norm eq 0 then
        vprintf JacHypHeight, 2: "  Precision loss!\n";
        vprintf JacHypHeight, 2:
                "   ==> increase precision and restart computation of infinite part\n";
        prec +:= 5;
        Rs0 := RealField(prec+5);
        bound +:= 5;
        flag := false;
        break n;
      end if;
      for j := 1 to 8 do s[j] /:= norm; end for;
      // add eps_infty
      pow4 *:= 4;
      sum_inf +:= Log(norm) / pow4;
    end for;
  until flag;
  vprintf JacHypHeight: " infinite part = %o.\n", sum_inf;
  height := ht + sum_inf + sum;
  height := ((Precision gt 0) select RealField(Precision)
                              else RealField())!height;
  vprintf JacHypHeight: "height(P) = %o.\n", height;
  C`HeightTable[P] := <height, Precision>;
  return height;
end intrinsic;*/
