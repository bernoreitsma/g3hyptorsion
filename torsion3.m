AttachSpec("spec");
import "heights.m": normalize;
import "transformations.m": KummerTransformation;

function counttwotorsiongens(J)
	C := Curve(J);
  f,h := HyperellipticPolynomials(C);
  assert h eq 0;
	fact := Factorization(f); // f is now of degree 8.
	fact1 := [ pair[1] : pair in fact | Degree(pair[1]) eq 1 ];
  fact2 := [ pair[1] : pair in fact | Degree(pair[1]) eq 2 ];
  fact3 := [ pair[1] : pair in fact | Degree(pair[1]) eq 3 ];
  fact4 := [ pair[1] : pair in fact | Degree(pair[1]) eq 4 ];	
	gensct := 0;
	gensct +:= (#fact1 ge 2) select #fact1 - 1 else 0;
	gensct +:= #fact2;
	gensct +:= (#fact1 ne 0) select #fact3  else 0;
	gensct +:= #fact4;
  if #fact1 + 2*#fact2 + ((#fact1 ge 1) select 3*#fact3 else 0) 
                + 4*#fact4 eq Degree(f) then gensct -:= 1; end if;
	return gensct;
end function;

intrinsic myTwoTorsionSubgroup(J::JacHyp) -> GrpAb, Map
{The rational 2-torsion subgroup of J for curves of genus 2 in simplified model.}
    if assigned J`TwoTorsion then 
      return J`TwoTorsion[1], J`TwoTorsion[2];
    end if;
    C := Curve(J);
    if Genus(C) ge 4 or Degree(C) mod 2 eq 1 then
      require Degree(C) mod 2 eq 1:
       "TwoTorsionSubgroup is currently only implemented for Jacobians",
       "of odd degree curves or genus 2 curves";
      f,h := HyperellipticPolynomials(C);
      require h cmpeq 0:
       "TwoTorsionSubgroup requires a curve in the form y^2 = f(x)";
      fact := Factorization(f);
      gens := Prune([J![ g[1],0] : g in fact ]); 
      G<[P]> := AbelianGroup([2 : i in [1..#gens]]);
	  L := [ J!0 ];
      for g in gens do L cat:= [ g + pt : pt in L ]; end for;
      iso := map< G -> J | g :-> &+[J | s[i]*gens[i] : i in [1..#s]]
          where s := Eltseq(g) >;
      J`TwoTorsion := <G, iso, L>;
      return G,iso;
    end if;
    
    // this part is added for genus 3, degree 8 curves.
    // (there is a write-up with a small justification)
    if Genus(C) eq 3 then
	  	f,h := HyperellipticPolynomials(C);
	  	require h cmpeq 0:
	  	  "TwoTorsionSubgroup requires a curve in the form y^2 = f(x)";
	  	fact := Factorization(f); // f is now of degree 8.
	  	fact1 := [ pair[1] : pair in fact | Degree(pair[1]) eq 1 ];
      fact2 := [ pair[1] : pair in fact | Degree(pair[1]) eq 2 ];
      fact3 := [ pair[1] : pair in fact | Degree(pair[1]) eq 3 ];
      fact4 := [ pair[1] : pair in fact | Degree(pair[1]) eq 4 ];
      if #fact1 ge 2 then
        gens := [ J ! [ pol1*fact1[i], 0 ] : i in [2..#fact1] ]
                where pol1 := fact1[1];
      else
        gens := [];
      end if;
      gens cat:= [ J ! [ pol, 0 ] : pol in fact2 ]; 
      if #fact1 ge 1 then
		 		gens cat:= [ J ! [pol*fact1[1], 0] : pol in fact3];
	  	end if;
      gens cat:= [ J ! [ pol, 0 ] : pol in fact4 ];
      if #fact1 + 2*#fact2 + ((#fact1 ge 1) select 3*#fact3 else 0) 
                + 4*#fact4 eq Degree(f) then Prune(~gens); end if;
      L := [ J!0 ];
      for g in gens do L cat:= [ g + pt : pt in L ]; end for;
      G<[P]> := AbelianGroup([ 2 : i in [1..#gens] ]);
      iso := map< G -> J | g :-> &+[J | s[i]*gens[i] : i in [1..#s]]
                                 where s := Eltseq(g) >;
      J`TwoTorsion := <G, iso, L>;
      return G, iso;    
    end if;
    require Genus(C) eq 2:
       "TwoTorsionSubgroup is currently only implemented for Jacobians",
       "of genus 2 curves.";
    f, h := HyperellipticPolynomials(C);
    require h eq 0:
       "TwoTorsionSubgroup requires a curve in the form y^2 = f(x).";
    fact := Factorization(f);
    // look for factors of degree 2
    fact1 := [ pair[1] : pair in fact | Degree(pair[1]) eq 1 ];
    fact2 := [ pair[1] : pair in fact | Degree(pair[1]) eq 2 ];
    if Degree(f) eq 5 then
      gens := [ J ! [pol, 0] : pol in fact1 ];
    elif #fact1 ge 2 then
      gens := [ J ! [ pol1*fact1[i], 0 ] : i in [2..#fact1] ]
              where pol1 := fact1[1];
    else
      gens := [];
    end if;
    gens cat:= [ J ! [ pol, 0 ] : pol in fact2 ];
    if #fact1 + 2*#fact2 eq Degree(f) then Prune(~gens); end if;
    L := [ J!0 ];
    for g in gens do L cat:= [ g + pt : pt in L ]; end for;
    G<[P]> := AbelianGroup([ 2 : i in [1..#gens] ]);
    iso := map< G -> J | g :-> &+[J | s[i]*gens[i] : i in [1..#s]]
                               where s := Eltseq(g) >;
    J`TwoTorsion := <G, iso, L>;
    return G, iso;
end intrinsic;

// The algorithm used in this function can be found on
// Canonical heights on the Jacobians ofcurves of genus 2 and the infinite descent
// by E.V. Flynn, N.P. Smart, Acta Arithmetica 79, part 4, 333-352.
function myHasPointOrder(C, P, n, B)
    // Tests whether P::KummerPt on C::CrvHyp (on K over the rationals) is a torsion
    // point of order n. B is a bound for the non-logarithmic naive height
    // of a torsion point.
    check := func< pt | Abs(pt[1]) gt B or Abs(pt[2]) gt B
                         or Abs(pt[3]) gt B or Abs(pt[4]) gt B 
                         or Abs(pt[5]) gt B or Abs(pt[6]) gt B
                         or Abs(pt[7]) gt B>;
    m := n;
    Px := KummerOrigin(C); Py := P; Pz := P;
    while true do
      if IsOdd(m) then
        Px := PseudoAdd(C, Px, Pz, Py);
        if check(Px) then return false; end if;
      else
        Py := PseudoAdd(C, Py, Pz, Px);
        if check(Py) then return false; end if;
      end if;
      m div:= 2;
      if m eq 0 then return Px eq KummerOrigin(C); end if;
      Pz := Double(C, Pz);
      if check(Pz) then return false; end if;
    end while;
end function;

function normalizetoaffine(seq)
	i := 1;
	while i ne 9 and not IsUnit(seq[i]) do i +:= 1; end while;
	newseq := [a / seq[i] : a in seq];
	return newseq;
end function;

function myLiftTorsionPoint(P, C, b, B: transmat := [1,0,0,1])
// (P::JacHypPt, C::CrvHyp, b::RngIntElt, B::FldReElt) -> BoolElt, JacHypPt
  // C = genus 3 curve over the rationals,
  // P = point on Jacobian over F_p,
  // b = bound for p-adic approximation precision.
  // B = height bound for torsion points
	f := HyperellipticPolynomials(C);
  p := #CoefficientRing(Parent(P));
	J := Jacobian(C);
  Jp := Parent(P);
  Dp := Curve(Jp);
	Cp := Curve(BaseChange(Jacobian(C), GF(p)));
	kumtransinv := KummerTransformation(Dp, Cp, ChangeUniverse(transmat, GF(p)));
  prec := 1;
  n := Order(P);
  if n eq 2 then
	  // this is a special case
	  tt := myTwoTorsionSubgroup(J);
	  tt := J`TwoTorsion[3];
	  K := KummerVarietyG3(C);
	  Kp := KummerVarietyG3(Dp);
	  PKp := ToKummerVariety(P);
	  for i := 2 to #tt do
			ttes := Eltseq(ToKummerVariety(tt[i]));
			integral_P := normalize(ttes);
	    if Kp!ChangeUniverse(integral_P, GF(p)) eq Kp!Eltseq(PKp) then return true, tt[i]; end if;
	  end for;
	  return false, _;
  end if;
	if n mod 2 eq 0 then
  	m := 1 - n; // smallest m congruent to 1 mod n
		doubleflag := false;
	else
  	a := EulerPhi(n);
		for d in Divisors(a) do
			if 2^d mod n eq 1 then
				order := d;
				break;
			end if;
		end for;
		m := 2^order;
		if (m - 1) mod p eq 0 then
			doubleflag := false;
			m := 1 - n;
		else
			doubleflag := true;
		end if;
  end if;
	K := KummerVarietyG3(C);
  // first lift
  F := GF(p);
  Kp := KummerVarietyG3(Curve(BaseChange(J, F)));
  PK:= Eltseq(kumtransinv(ToKummerVariety(P)));
  // applies LLL-reduction to find a short vector. 
  L := Lattice(8, ChangeUniverse(Eltseq(PK), Integers())
                   cat [p,0,0,0,0,0,0,0, 0,p,0,0,0,0,0,0, 0,0,p,0,0,0,0,0, 0,0,0,p,0,0,0,0,
						0,0,0,0,p,0,0,0, 0,0,0,0,0,p,0,0, 0,0,0,0,0,0,p,0, 0,0,0,0,0,0,0,p]);
  app := Eltseq(Basis(L)[1]);
  while prec lt b do
    // next lift
    newprec := Min(2*prec,b);
		oldF := F;
    F := Integers(p^newprec);
    // Onew := O(F!p^newprec);
		OldKp := Kp;
    Kp := KummerVarietyG3(C: Ambient := ProjectiveSpace(F, 7));
    // lift point to P^7 with new precision
    s := ChangeUniverse(Eltseq(PK), Integers()); 
    // uses a step in multivariate Newton Iteration to ensure that s
    // lifts to a point on the Kummer with sufficient precision.
		P_int := ChangeUniverse(Eltseq(s), Integers());
    kv := -Vector(oldF, [oldF| ExactQuotient(Evaluate(eqn, P_int), p^prec) : eqn in Equations(K)]); 
		jac := JacobianMatrix(DefiningEquations(OldKp));
    dkv := Matrix(oldF, [[Evaluate(jac[i,j], Eltseq(PK)) : j in [1..NumberOfColumns(jac)]]
                      : i in [1..NumberOfRows(jac)]]);
    if Rank(dkv) lt 4 then
			print "Working on point:", s;
      error "Singularity detected!";
    end if;
		sol, ker := Solution(Transpose(dkv), kv);
		sol := ChangeRing(sol, Integers());
		s1 := s;
		s1 := Vector(s) + p^prec * sol; // this is the actual Newton iteration step.
		if not doubleflag then	
			s2 := Kp!Eltseq(Multiple(C, m, Kp!Eltseq(s1) : Ambient := ProjectiveSpace(F, 7)));
		else
			s2 := s1;
			for i := 1 to order do
				s2 := Double(C, Kp!Eltseq(s2) : Ambient := ProjectiveSpace(F, 7));
			end for;
		end if;
		s1 := ChangeRing(s1, F);	
		s1 := normalizetoaffine(Eltseq(s1));		
		s2 := normalizetoaffine(Eltseq(s2));
		i := 1;
		while i ne 9 and Integers() ! (s1[i] - s2[i]) mod p^prec eq 0 do i +:= 1; end while;
		if i ne 9 then print p, prec, s1, s2; end if;
	  error if i ne 9,
	        "LiftTorsionPoint: Precision loss!!";

	  PK := [F | (m*(Integers()!s1[i]) - Integers()!s2[i])/(m-1) : i in [1..8] ];  
	  // compute approximation
	  q := p^newprec;
	  L := Lattice(8, ChangeUniverse(PK, Integers())
	                   cat [q,0,0,0,0,0,0,0, 0,q,0,0,0,0,0,0, 0,0,q,0,0,0,0,0, 0,0,0,q,0,0,0,0,
						0,0,0,0,q,0,0,0, 0,0,0,0,0,q,0,0, 0,0,0,0,0,0,q,0, 0,0,0,0,0,0,0,q]);
	  app1 := Eltseq(Basis(L)[1]);
	  // check if the candidate already lifts
	  if app eq app1 and IsPointOnKummer(C, app1) then
	    PQ := K!app1;
	    if myHasPointOrder(C, PQ, n, B) then	
				if Degree(f) eq 7 then
	      	PJ := LiftToJacobian(C, PQ);
	      	if IsEmpty(PJ) then
	     	  	return false, _;
	      	else
	        	return true, PJ[1];
	      	end if;
				else return doesLiftToJacobian(C, PQ), _; end if;   
			end if;
	  end if;
	  prec := newprec; app := app1;
	end while;
	// now prec = b. Check if found
	if not IsPointOnKummer(C, app) then return false, _; end if;
	PQ := K!app;
	//Bug fix by Steve:
	//if not HasPointOrder(C, P, n, B) then return false, _; end if;
	if not myHasPointOrder(C, PQ, n, B) then return false, _; end if;
	if Degree(f) eq 7 then
		PJ := Points(J, PQ);
		if IsEmpty(PJ) then return false, _; else return true, PJ[1]; end if;
	else
		return doesLiftToJacobian(C, PQ), _;
	end if;
end function;



/* The code of this function compares well to Stoll's paper on genus 2
curves [1], section 11, the second algorithm (bottom of pg. 200). 
This function translates almost immediately to the genus 3 case,
except if we need a transformation of coordinates to bring a non-ramified
point to infinity. (See transformation from im. hyp. curve to real hyp. curve. */

intrinsic myTorsionSubgroup(J::JacHyp)
    -> GrpAb, Map
{Finds the rational torsion subgroup of J. The curve of J must have genus 2
 and be defined over the rationals and have form  y^2 = f(x)  with integral 
 coefficients. Second value gives the map from the group into J. }
    
    // if attribute is already assigned, don't run the calculation again.
    /*if assigned J`TorsionGroup then
      return J`TorsionGroup, J`TorsionMap;
    end if;*/
    
    tstart := Cputime();
    tlift := 0.0;
    C := Curve(J);
    require Genus(C) eq 3 and CoefficientRing(C) cmpeq Rationals():
            "This function is designed",
            "for Jacobians of genus 3 curves over the rationals.";
    f, h := HyperellipticPolynomials(C);
    require h eq 0 and &and[ Denominator(c) eq 1 : c in Coefficients(f)]:
            "TorsionSubgroup needs a curve of the form  y^2 = f(x),",
            "where f has integral coefficients.";
    vprint JacHypTorsion: "TorsionSubgroup of J = \n",J;
		
		flaglt := not HasOddDegreeModel(C) and #PointsAtInfinity(C) eq 0;    		

		if Degree(f) eq 8 and HasOddDegreeModel(C) then
			_, D, trans := HasOddDegreeModel(C);
			DS, DStrans := SimplifiedModel(D);
			DI, DItrans := IntegralModel(DS);
			D := DI; trans := trans * DStrans * DItrans;
			JD := Jacobian(D);
			G, iso := myTorsionSubgroup(JD);
			transinv := Inverse(trans);
			Jtransinv := map<JD -> J | P :-> Evaluate(transinv, P)>;
			return G, iso*Jtransinv;
		end if;

    bound := HeightConstantG3(J);
    // This bounds the logarithmic naive height of the torsion points
    vprint JacHypTorsion: " Height Constant =",bound;
    Bound := Exp(bound);           // non-log height bound
			// changed in order to be safe for now.
    bound1 := Log(2048.0) + 2*bound; // bound for p-adic precision
    // Get a bound for the order of the torsion subgroup
    //  (by looking at the reduction at a few good primes).
    tb := TorsionBound(J, 10);
    tb1 := J`TorsionBound[3];
    fact := Factorization(tb);
    vprintf JacHypTorsion: " Torsion Bound = %o, factored: %o\n",tb,fact;
    // Initialize data for group.
    ed := [];      // elementary divisors
    gL := [ J | ]; // generators
		ttc := counttwotorsiongens(J);
    for pair in fact do
      q := pair[1];
      vprintf JacHypTorsion: "  Determining %o-part...\n",q;
      // Find p such that J(F_p) has minimal p-valuation and p ne q.
			if flaglt then
				minval := 1000;
				for t in tb1 do
					if Valuation(t[2],q) lt minval and #Points(Curve(BaseExtend(J, GF(t[1])))) ne 0 and t[1] ne q then
						p := t[1];
						minval := Valuation(t[2],q);
					end if;
				end for;
			else
      	e, pos := Min([ Valuation(t[2],q) + (t[1] eq q select 1000 else 0) :
                      t in tb1]);
      	p := tb1[pos][1];
			end if;
      vprintf JacHypTorsion:
              "   Using prime %o; %o-torsion has order %o^%o\n",p,q,q,e;
      pbound := Ceiling(bound1/Log(p));
      vprintf JacHypTorsion: "   Approximation up to O(%o^%o)\n",p,pbound;
      // Compute q-subgroup of J(F_p)		
      Jp := BaseExtend(J, GF(p));

			if flaglt then
				Cp := Curve(Jp);
				if #PointsAtInfinity(Cp) ge 1 then
					mat := [1,0,0,1];
					Dp := Cp;
					JDp := Jacobian(Dp);
				else
					pts := Points(Cp);
					x1 := Eltseq(pts[1])[1];
					mat := [GF(p) |0,1,1,-x1];
					Dp, _ := Transformation(Cp, mat);
					JDp := Jacobian(Dp);
				end if;
			end if;

      if GetVerbose("JacHypTorsion") gt 0 then
        Kp := BaseExtend(KummerVarietyG3(C), GF(p));
      end if;
			if flaglt then
				Gp, mp := Sylow(JDp, q);
			else
				Gp, mp := Sylow(Jp, q);
			end if;
      inv := Invariants(Gp);
      vprintf JacHypTorsion: "   Structure of %o-subgroup: %o\n",q,inv;
      // Determine subgroup of points that lift to J(Q)
      Tcurr := sub<Gp |>;
      Tgens := [Gp | ];
			if Degree(f) eq 7 then
      	Tgimages := [J | ];
			end if;
      Gcurr, qmap := quo<Gp | Tcurr>;
      S0 := { Gcurr | 0 };
      S1 := Set(Gcurr) diff S0;
      while not IsEmpty(S1) do
        vprint JacHypTorsion:
               "    Current subgroup has invariants", Invariants(Tcurr);
        vprint JacHypTorsion:
               "     There are at most",#S1 div (q-1),"elements to be tested.";
        // Choose some element in S1
        g := Rep(S1);
        // Make it primitive
        g := Gcurr![ s div gcd : s in gs ]
               where gcd := GCD(gs)
               where gs := Eltseq(g);
        // Find smallest j such that q^j*g lifts
        j := 0; gg := g;
        while gg ne Gcurr!0 do
          gl := gg @@ qmap; // Some preimage in Gp
          pt := mp(gl);     // and the corresponding point on J(F_p)
          vprint JacHypTorsion: "     Trying to lift point",pt,"...";
          vprintf JacHypTorsion, 2:
                  "     Image on Kummer surface = %o\n", Kp!pt;
          tt := Cputime();
					if flaglt and Order(pt) eq 2 then
						flag := false;
					elif flaglt then
						flag := myLiftTorsionPoint(pt, C, pbound, Bound: transmat := mat);
					else
          	flag, lift := myLiftTorsionPoint(pt, C, pbound, Bound); // Lift
					end if;          
					tlift +:= Cputime(tt);
          if flag and Degree(f) eq 7 then 
            vprintf JacHypTorsion: "     Point lifts";
            vprintf JacHypTorsion, 2: " to %o", lift;
            vprintf JacHypTorsion: "\n";
            break;
          elif flag then
						vprint JacHypTorsion: "     Points Lift (non-explicitly)";
						break;
					else
            vprint JacHypTorsion: "     Point does not lift";
          end if;
          j +:= 1;
          gg := q*gg;
        end while; // gg ne Gcurr!0
        // Here, gg = q^j*g, and gl is a preimage of gg in Gp
        if gg ne Gcurr!0 then
          // Can enlarge current subgroup
          Append(~Tgens, gl);
					if Degree(f) eq 7 then
          	Append(~Tgimages, lift);
					end if;
          Tcurr := sub<Gp | Tcurr, gl>;
          Gcurr, qmap1 := quo<Gcurr | gg>;
          qmap := qmap*qmap1;
          // Note new elements we know don't lift
          S0 := qmap1(S0) join { k*g1 : k in [1..q^j-1] } where g1 := qmap1(g);
          S1 := Set(Gcurr) diff S0;
					if q eq 2 then
						ttc -:= 1;
					end if;
        else // gg eq Gcurr!0
          // Note new elements we know don't lift
          Snew := { k*g : k in [1..q^j-1] };
          S0 join:= Snew;
          S1 diff:= Snew;
        end if; // gg ne Gcurr!0
      end while; // not IsEmpty(S1)
      // Now, Tcurr is the subgroup of Gp of points that lift to J(Q).
      // Find generators in J(Q).
			invs := Invariants(Tcurr);
		  vprintf JacHypTorsion:
		          "   The %o-part of the torsion subgroup has invariants %o\n",
		          q, invs;
			if flaglt and q eq 2 then
				invs := invs cat [2 : i in [1..ttc]];
			end if;
			if Degree(f) eq 7 then
		    if not IsEmpty(Tgens) then
		      // This `if' is necessary since Magma 2.4 barfs on
		      //  hom< G -> G | [G|] > where G := FreeAbelianGroup(0)
		      vprintf JacHypTorsion:
		              "  Determining generators for the %o-part...\n",q;
		      qqmap := hom< FreeAbelianGroup(#Tgens) -> Tcurr | Tgens >;
		      Lp1 := [ &+[ s[j]*Tgimages[j] : j in [1..#s] ]
		               where s :=  Eltseq(Tcurr.i @@ qqmap)
		               : i in [1..#invs] ];
		      if GetVerbose("JacHypTorsion") ge 2 then
		        print "   Generators with their orders:";
		        for i := 1 to #invs do
		          print "    ", Lp1[i], ",  of order", invs[i];
		        end for;
		      end if; // GetVerbose("JacHypTorsion") ge 2
	 
		      // Now put q-part together with what we've got so far.
		      d := #invs-#ed;
		      vprintf JacHypTorsion:
		              "  Combining %o-part with what we've already got...\n",q;
		      if d gt 0 then
		        ed := invs[[1..d]] cat [ Lcm(ed[i], invs[i+d]) : i in [1..#ed] ];
		        gL := Lp1[[1..d]] cat [ gL[i] + Lp1[i+d] : i in [1..#gL] ];
		      else
		        ed := ed[[1..-d]] cat [ Lcm(ed[i-d], invs[i]) : i in [1..#invs] ];
		        gL := gL[[1..-d]] cat [ gL[i-d] + Lp1[i] : i in [1..#Lp1] ];
		      end if;
		    end if; // not IsEmpty(Tgens)
		    vprint JacHypTorsion: "  Current invariants:",ed;
			else // Degree(f) ne 7
				if invs ne [] then
					d := #invs - #ed;
		      if d gt 0 then
		        ed := invs[[1..d]] cat [ Lcm(ed[i], invs[i+d]) : i in [1..#ed] ];
					else
		        ed := ed[[1..-d]] cat [ Lcm(ed[i-d], invs[i]) : i in [1..#invs] ];
					end if;
				end if;
			end if;											
    end for; // pair in fact
    vprintf JacHypTorsion: "\n";
 
		// Construct the abstract group
		G<[P]> := AbelianGroup(ed);   
		if Degree(f) eq 7 then 
		  vprint JacHypTorsion: " Torsion subgroup has structure", ed;
		  if GetVerbose("JacHypTorsion") ge 2 and not IsEmpty(ed) then
		    print "   Generators with their orders:";
		    for i := 1 to #ed do
		      print "    ", gL[i], ",  of order", ed[i];
		    end for;
		  end if;
		  vprintf JacHypTorsion: "\n";
		  // Construct the isomorphism from the abstract group to the points on J
		  iso := map< G -> J | g :-> &+[ J | s[i]*gL[i] : i in [1..#s]]
		                             where s := Eltseq(g) >;
		  J`TorsionGroup := G; J`TorsionMap := iso;
		  t := Cputime(tstart);
		  vprintf JacHypTorsion: "Time used for lifting: %o ms\n", Round(1000*tlift);
		  vprintf JacHypTorsion: "Total time:            %o ms\n\n", Round(1000*t);
		  return G, iso;
		else
			return G;
		end if;
end intrinsic;


/* References
[1] Michael Stoll - On the Height constant for curves of genus two.
[2] P. Lockhart - On the Discriminant of Hyperelliptic Curves.
[3] Michael Stoll - An Explicit Theory of heights for Hyperelliptic
    Jacobians of Genus Three
[4] J.S. Müller - Explicit Kummer Varieties of hyperelliptic Jacobian Threefolds
[5] E. V. Flynn, N.P. Smart - Canonical Heights of Jacobians of Genus 2 and the infinite
    descent
[6] Michael Stoll - Arithmetic of Hyperelliptic Curves
*/
