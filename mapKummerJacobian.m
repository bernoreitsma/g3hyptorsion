/* The maps from the Jacobian to the Kummer and the lift that maps a point on the Kummer to its pre-image on the same map.
	ToKummerVariety: Given P on the Jacobian(C), gives the image of P on the Kummer Variety.
	LiftToJacobian: Given a curve C, P on the Kummer Variety of C, gives the points on Jacobian(C) that map to P*/

Attach("G3HypHelp.m");
import "G3HypHelp.m": K3quartics, K3deltas, Xipolynomials, K3biquforms, K3xi2coeffs;

// We store the data with the curve

declare attributes CrvHyp:
 KummerEquations, KummerVariety, KummerDeltas, KummerXipols, KummerBQF, HeightTable;

declare verbose ReducedBasis, 2;

declare verbose FindPointsG3, 3;

import "JacobianPoints.m": ToJacobian;

// this functino returns the form \eta_{ij} as described in [3], Section 2.
function eta(apolcfs, bpolcfs, cpolcfs, i, j)
    assert i le j;
    if i eq j then
        return bpolcfs[i+1]^2 - apolcfs[i+1]*cpolcfs[i+1];
    else // we assume i < j from function calls (could be improved)
        return 2*bpolcfs[i+1]*bpolcfs[j+1] - apolcfs[i+1]*cpolcfs[j+1] - apolcfs[j+1]*cpolcfs[i+1];
    end if;
end function;

// Computes image under kappa: J --> K of a point P on J.

intrinsic ToKummerVariety(P::JacHypPt : twist := 1, Kum := "UNIQUE") -> Pt
{Returns the image of P on the Kummer variety of its parent (genus 3).}
    // create structures associated with the given P and its parent.
    Ct := Curve(Parent(P));
    C := twist eq 1 select Ct else HyperellipticCurve(HyperellipticPolynomials(Ct)/twist);
    K := Kum cmpeq "UNIQUE" select KummerVarietyG3(C) else Kum;
    fpol := HyperellipticPolynomials(C);
    F := BaseRing(Parent(fpol));
    // extract defining objects for P (Mumford Representation)
    apol := P[1];
    bpol := P[2];
    deg := P[3];
    cpol := ExactQuotient(bpol^2 - fpol*twist, apol); // uses eq. (2.1) in [3]
    if deg eq 0 then
        return KummerOrigin(C);
    elif deg eq 1 then // Point of degree 1. DegF = 7.
        a0, a1 := Explode(Coefficients(apol));
        coords := [F| 0, 0, 0, 0, a1^2, a0*a1, a0^2];
        G := 2*Coefficient(fpol, 8)*a0^4 - a1*Coefficient(fpol, 7)*a0^3;
        Append(~coords, -G/a1^2);
        return K!coords;
    elif deg eq 2 then
		if Degree(apol) eq 0 then // two points at infinity added up to each other (degF = 8)
			xi8 := 4*Coefficient(fpol, 6) * Coefficient(fpol, 8) - Coefficient(fpol, 7)^2;		
			return K![F|0,0,0,0,0,0, 4*Coefficient(fpol, 8) ,xi8];
        elif Degree(apol) eq 1 then	// One affine point, DegF = 8.
            a0, a1 := Explode(Coefficients(apol));
            x1 := -a0/a1;
            /*if Evaluate(bpol, x1) eq 0 then // affine point is two-torsion
                coords := [F|0,0,0,0,1,-x1,x1^2];
                xi8 := -2*x1^4*Coefficient(fpol, 8) - x1^3*Coefficient(fpol, 7);
                Append(~coords, xi8);
                return K!coords;
			elif x1 ne 0 then*/
                coords := [F| 0, 0, 0, 0, 1, -x1, x1^2]; // compute first 7 coordinates
                w1 := Evaluate(bpol, x1);
                w2 := Coefficient(bpol, 4);
                xi8 := 2*w1*w2 - 2*x1^4*Coefficient(fpol, 8) - x1^3*Coefficient(fpol, 7); // compute G.
                Append(~coords, xi8);
                return K!coords;
            /*else // x1 = 0
                flag, sqrtf0f8 := IsSquare(Coefficient(fpol, 0) * Coefficient(fpol, 8));
                assert flag; // two rat. pts at infinity, (0,y) on C --> f0, f8 are squares.
                sign := Coefficient(bpol, 4) * Evaluate(bpol, 0);
                return K ! [F|0,0,0,0,1,0,0,2*sign*sqrtf0f8];
            end if;*/
        elif Degree(apol) eq 2 then // 
            a0, a1, a2 := Explode(Coefficients(apol));
            b0, b1 := Explode([Coefficient(bpol, j) : j in [0..1]]);
            // first 7 coords
            coords := [F| 0, a2^2, a1*a2, a0*a2, a1^2 - a0*a2, a0*a1, a0^2];
            if a1^2 ne 4*a0*a2 then // the if-else structure computes xi_8.
                // two distinct points: (x_1 - x_2)^2 = a1^2 - 4*a0*a2 (Discriminant)
                G := 2*&+[Coefficient(fpol, 2*j)*a0^j*a2^(4-j) : j in [0..4]]
                  - a1*&+[Coefficient(fpol, 2*j+1)*a0^j*a2^(3-j) : j in [0..3]];
                y1y2 := (b1^2*a0 - b0*b1*a1 + b0^2*a2)/twist;
                Append(~coords, (2*y1y2 - G)/(a1^2 - 4*a0*a2));
            else
                f0,f1,f2,f3,f4,f5,f6,f7,f8 := Explode([Coefficient(fpol, j) : j in [0..8]]);
                s0,s1,s2 := Explode([a2,a1,a0]);
                cof1 := 4*f0*s0^4 - 2*f1*s0^3*s1 + 4*f2*s0^3*s2 - 2*f3*s0^2*s1*s2
                    + 4*f4*s0^2*s2^2 - 2*f5*s0*s1*s2^2 + 4*f6*s0*s2^3 - 2*f7*s1*s2^3
                    + 4*f8*s2^4;
                assert cof1 ne 0;
                cof0 := (-4*f0*f2 + f1^2)*s0^6 + 4*f0*f3*s0^5*s1 - 2*f1*f3*s0^5*s2
                    - 4*f0*f4*s0^4*s1^2 + (-4*f0*f5 + 4*f1*f4)*s0^4*s1*s2
                    + (-4*f0*f6 + 2*f1*f5 - 4*f2*f4 + f3^2)*s0^4*s2^2 + 4*f0*f5*s0^3*s1^3
                    + (8*f0*f6 - 4*f1*f5)*s0^3*s1^2*s2
                    + (8*f0*f7 - 4*f1*f6 + 4*f2*f5)*s0^3*s1*s2^2
                    + (-2*f1*f7 - 2*f3*f5)*s0^3*s2^3 - 4*f0*f6*s0^2*s1^4
                    + (-12*f0*f7 + 4*f1*f6)*s0^2*s1^3*s2
                    + (-16*f0*f8 + 8*f1*f7 - 4*f2*f6)*s0^2*s1^2*s2^2
                    + (8*f1*f8 - 4*f2*f7 + 4*f3*f6)*s0^2*s1*s2^3
                    + (-4*f2*f8 + 2*f3*f7 - 4*f4*f6 + f5^2)*s0^2*s2^4
                    + 4*f0*f7*s0*s1^5 + (16*f0*f8 - 4*f1*f7)*s0*s1^4*s2
                    + (-12*f1*f8 + 4*f2*f7)*s0*s1^3*s2^2 + (8*f2*f8 - 4*f3*f7)*s0*s1^2*s2^3
                    + (-4*f3*f8 + 4*f4*f7)*s0*s1*s2^4 - 2*f5*f7*s0*s2^5 - 4*f0*f8*s1^6
                    + 4*f1*f8*s1^5*s2 - 4*f2*f8*s1^4*s2^2 + 4*f3*f8*s1^3*s2^3
                    - 4*f4*f8*s1^2*s2^4 + 4*f5*f8*s1*s2^5 + (-4*f6*f8 + f7^2)*s2^6;
                Append(~coords, -cof0/cof1);
            end if;
            return K!coords;
        end if;
    else // deg is now ge 3
        a0, a1, a2, a3, a4 := Explode([Coefficient(apol, i) : i in [0..4]]);
        b0, b1, b2, b3, b4 := Explode([Coefficient(bpol, i) : i in [0..4]]);
        c0, c1, c2, c3, c4 := Explode([Coefficient(cpol, i) : i in [0..4]]);
        apolcfs := [a0, a1, a2, a3, a4];
        bpolcfs := [b0, b1, b2, b3, b4];
        cpolcfs := [c0, c1, c2, c3, c4];
        coords := [F| twist, eta(apolcfs, bpolcfs, cpolcfs, 2, 4), eta(apolcfs, bpolcfs, cpolcfs, 1, 4),
                    eta(apolcfs, bpolcfs, cpolcfs, 0, 4),
                    eta(apolcfs, bpolcfs, cpolcfs, 0, 4) + eta(apolcfs, bpolcfs, cpolcfs, 1, 3),
                    eta(apolcfs, bpolcfs, cpolcfs, 0, 3), eta(apolcfs, bpolcfs, cpolcfs, 0, 2)];
        Append(~coords, (coords[2]*coords[7] - coords[3]*coords[6] + coords[4]*coords[5])/twist);
        return K!coords;
    end if;
end intrinsic;

// computes whether a point R on K(Q) has a pre-image on J(Q) or not.

intrinsic doesLiftToJacobian(C::CrvHyp, P::Pt : twist := 1) -> SetIndx[JacHypPt]
{Decides whether a point lifts to the jacobian or not}
    Ct := twist eq 1 select C else QuadraticTwist(C, twist);
    xiseq := Eltseq(P);
    f := HyperellipticPolynomials(C);
	f0, f1, f2, f3, f4, f5, f6, f7, f8 := Explode(Coefficients(f));
    Pol := Parent(f);
    f0,f1,f2,f3,f4,f5,f6,f7,f8 := Explode([Coefficient(f, i) : i in [0..8]]);
    if xiseq[1] ne 0 then // this case is described in [3] - the start of section 4.
        // normalize first coordinate to be 1
        x2,x3,x4,x5,x6,x7 := Explode([xi/xiseq[1] : xi in xiseq[2..7]]);
        // set up matrix, found in [3], equation (2.7).
        mat := Matrix([[2*f0,        f1,        x7,        x6,   x4],
                       [  f1, 2*(f2-x7),     f3-x6,     x5-x4,   x3],
                       [  x7,     f3-x6, 2*(f4-x5),     f5-x3,   x2],
                       [  x6,     x5-x4,     f5-x3, 2*(f6-x2),   f7],
                       [  x4,        x3,        x2,        f7, 2*f8]]);
        // test minors
        for s in Subsets({1..5}, 3) do
            ss := Setseq(s);
            submat := Matrix([[mat[i,j] : j in ss] : i in ss]);
            minor := Determinant(submat);
            if minor ne 0 and not IsSquare(-1/2*minor*twist) then
                return false;
			end if;
		end for;
        return true;	// two-torsion point
    elif xiseq[2] ne 0 then	// deg(P) = 2 and P lives in the support of the theta divisor.
	    x1x2 := xiseq[4]/xiseq[2];
	    sumx1x2 := [(-xiseq[3]/xiseq[2])^i : i in [1..8]];
        for j := 2 to 8 do
            for l := 1 to Floor(j/2) do
                sub := (j eq 2*l) select Binomial(j, l)*x1x2^l else Binomial(j, l)*sumx1x2[j - 2*l]*x1x2^l;
                sumx1x2[j] -:= sub; // sumx1x2[j] = x1^j + x2^j
            end for;
        end for;
        Da := sumx1x2[2] - 2*x1x2;
        Gx1x2 := 2*(f0 + f2*x1x2 + f4*x1x2^2 + f6*x1x2^3 + f8*x1x2^4)
            + sumx1x2[1]*(f1 + f3*x1x2 + f5*x1x2^2 + f7*x1x2^3);
        y1y2_t_2 := xiseq[8]/xiseq[2] * Da + Gx1x2;
        sumy1y2sq := f8*sumx1x2[8] + f7*sumx1x2[7] + f6*sumx1x2[6] + f5*sumx1x2[5]
            + f4*sumx1x2[4] + f3*sumx1x2[3] + f2*sumx1x2[2] + f1*sumx1x2[1] + 2*f0;
        if not IsSquare(sumy1y2sq + y1y2_t_2) then return false; end if;
        // need y1+y2 in k, so y_1^2 + y_2^2 + 2*y1y2 in k^2
        Db := sumy1y2sq - y1y2_t_2; // y_1^2 + y_2^2 - 2*y1y2
        //"Da=", Da; "Db=", Db;
        if Da eq 0 then return true; end if;
        return IsSquare(Db/Da);
    else
        assert xiseq[3] eq 0 and xiseq[4] eq 0;
        if xiseq[5] eq 0 then
            if xiseq[6] eq 0 and xiseq[7] eq 0 then
                return true; // origin
            else
                assert xiseq[6] eq 0; // 2*infty_1 - m or 2*infty_2 - m
                return #PointsAtInfinity(C) eq 2;
            end if;
        else // degree one affine point
            // jsm: modified 24-10-22
            x0 := -xiseq[6]/xiseq[5];
            return IsSquare(Evaluate(f*twist, x0));
        end if;					
    end if;
end intrinsic;

// explicitly computes the pre-image of a point R on K under \kappa, works only for the cases where
// we can find a unique (Mumford) representation of this pre-image.

intrinsic LiftToJacobian(C::CrvHyp, P::Pt : twist := 1) -> SetIndx[JacHypPt]
{Given a point P on the Kummer variety associated to C, returns the rational points
on the Jacobian of C that map to P.}
  assert Ring(Parent(P)) eq /*KummerVarietyG3(C)*/(BaseRing(C)); // why is the commented part there?
  Ct := twist eq 1 select C else QuadraticTwist(C, twist);
  xiseq := Eltseq(P);
  f := HyperellipticPolynomials(C);
  Pol := Parent(f);
  f0,f1,f2,f3,f4,f5,f6,f7,f8 := Explode([Coefficient(f, i) : i in [0..8]]);
  if xiseq[1] ne 0 then
    // normalize first coordinate to be 1
    x2,x3,x4,x5,x6,x7 := Explode([xi/xiseq[1] : xi in xiseq[2..7]]);
    // set up matrix, found in [3], equation (2.7).
    mat := Matrix([[2*f0,        f1,        x7,        x6,   x4],
                   [  f1, 2*(f2-x7),     f3-x6,     x5-x4,   x3],
                   [  x7,     f3-x6, 2*(f4-x5),     f5-x3,   x2],
                   [  x6,     x5-x4,     f5-x3, 2*(f6-x2),   f7],
                   [  x4,        x3,        x2,        f7, 2*f8]]);
    // test minors
    for s in Subsets({1..5}, 3) do
      ss := Setseq(s);
      submat := Matrix([[mat[i,j] : j in ss] : i in ss]);
      minor := Determinant(submat);
      if minor ne 0 then
        // sqrtmin is mu as defined in [3] eqn (4.1)
        flag, sqrtmin := IsSquare(-1/2*minor*twist);
        if flag then
          // point should lift
          // find kernel (dim = 2)
          // see section 4 of [3].
          kermat := KernelMatrix(mat);
          assert NumberOfRows(kermat) eq 2;
          trmat := Matrix([kermat[1], kermat[2]]
                           cat [Parent(kermat[1]) |
                                Vector([i eq j select 1 else 0 : i in [1..5]])
                                 : j in ss]);
          // parametrize the conic
          Con := Conic(submat);
          para := Parametrization(Con);
          pareqn := DefiningPolynomials(para);
          P2 := Universe(pareqn);
          mat1 := Matrix([[MonomialCoefficient(eqn, mon)
                            : mon in [P2.1^2, P2.1*P2.2, P2.2^2]]
                           : eqn in pareqn]);
          trmat := Matrix([[i le 2 or j le 2 select (i eq j select 1 else 0)
                                             else mat1[j-2,i-2]
                              : j in [1..5]] : i in [1..5]])
                    * trmat;
          // now trmat*mat*Transpose(trmat) has constant times antidiag(1,-2,1)
          // in its lower right 3x3 submatrix and zeros elsewhere
          // up to constant factor
          trmat := Transpose(trmat^-1)*sqrtmin;
          Apol := Pol!Eltseq(trmat[3]);
          Bpol := Pol!Eltseq(trmat[4]);
          Cpol := Pol!Eltseq(trmat[5]);
          flag, qu := IsDivisibleBy(f, Bpol^2 - Apol*Cpol);
          assert flag;
          flag, sqrtqu := IsSquare(qu*twist);
          assert flag;
          Apol *:= sqrtqu;
          Bpol *:= sqrtqu;
          Cpol *:= sqrtqu;
          // now normalize to have deg(Apol) le 3
          ptJ := ToJacobian(Jacobian(Ct), Apol, Bpol, Cpol);
          return {@ ptJ, -ptJ @};
        else
          // point does not lift
          return {@ @};
        end if;
      end if;
    end for;
    // all minors vanish ==> 2-torsion point
    // find kernel (dim = 3)
    for s in Subsets({1..5}, 2) do
      ss := Setseq(s);
      submat := Matrix([[mat[i,j] : j in ss] : i in ss]);
      minor := Determinant(submat);
      if minor ne 0 then
        kermat := KernelMatrix(mat);
        assert NumberOfRows(kermat) eq 3;
        trmat := Matrix([kermat[1], kermat[2], kermat[3]]
                          cat [Parent(kermat[1]) |
                                Vector([i eq j select 1 else 0 : i in [1..5]])
                                : j in ss]);
        pol := Pol![submat[2,2], 2*submat[1,2], submat[1,1]];
        mat1 := IdentityMatrix(BaseRing(trmat), 5);
        if Degree(pol) eq 1 then
          mat1[5,4] := -Coefficient(pol, 0);
          mat1[5,5] := Coefficient(pol, 1);
        else
          roots := [r[1] : r in Roots(pol)];
          assert #roots eq 2;
          mat1[4,4] := roots[1];
          mat1[4,5] := 1;
          mat1[5,4] := roots[2];
          mat1[5,5] := 1;
        end if;
        trmat := mat1*trmat;
        trmat := Transpose(trmat^-1);
        Apol := Pol!Eltseq(trmat[4]);
        Cpol := Pol!Eltseq(trmat[5]);
        flag, scal := IsDivisibleBy(f*twist, Apol*Cpol);
        assert flag;
        return {@ ToJacobian(Jacobian(Ct), scal*Apol, Pol!0, Cpol) @};
       end if;
    end for;
  elif xiseq[2] ne 0 then
    // xi1 = 0, xi2 /= 0 : degree 2 point
    // get polynomial A
    Apol := Pol![xiseq[4]/xiseq[2], xiseq[3]/xiseq[2], 1];
    cands := Points(Jacobian(Ct), Apol); // get possible points
    return {@ pt : pt in cands | ToKummerVariety(pt : twist := twist, Kum := Parent(P)) eq P @};
  else // degree 1 point (0 : 0 : 0 : 0 : 1 : -x0 : x0^2 : ...)
    assert xiseq[3] eq 0 and xiseq[4] eq 0;
    if xiseq[5] eq 0 then
      // origin
      assert xiseq[6] eq 0 and xiseq[7] eq 0;
      return {@ Jacobian(C)!0 @};
    else
      x0 := -xiseq[6]/xiseq[5];
      flag, y0 := IsSquare(Evaluate(f*twist, x0));
      if flag then
        ptJ := ToJacobian(Jacobian(Ct), Pol.1 - x0, Pol!y0, ExactQuotient((Pol!y0)^2 - f, Pol.1 - x0));
        return {@ ptJ, -ptJ @};
      else
        return {@ @};
      end if;
    end if;
  end if;
  return {@ @};
end intrinsic;
