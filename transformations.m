import "torsion3.m": normalizetoaffine;

function G_func(fpol, seq)
	f0,f1,f2,f3,f4,f5,f6,f7,f8 := Explode([Coefficient(fpol, i) : i in [0..8]]);
	sumx1x2 := -seq[3];
	prodx1x2 := seq[4];
	return 2*(f0 + f2*prodx1x2 + f4*prodx1x2^2 + f6*prodx1x2^3 + f8*prodx1x2^4)
				 + sumx1x2*(f1 + f3*prodx1x2 + f5*prodx1x2^2 + f7*prodx1x2^3);
end function;

function solveforxi8(f,g,oldseq, newseq, ti, ui)
	Prune(~newseq);
	if newseq eq [0,0,0,0,0,0,0] then
		return 1;
	end if;
	if newseq[5] eq 3*newseq[4] then // discriminant eq 0, 2*(x_1, y_1) + m
		i := 1;
		while newseq[i] eq 0 do i +:= 1; end while;
		if i eq 7 then // two equal points at infinity.
			return ExactQuotient(4*Coefficient(g, 6) * Coefficient(g, 8) - Coefficient(g, 7)^2, 4*Coefficient(g,8));		
		end if;
		f0,f1,f2,f3,f4,f5,f6,f7,f8 := Explode([Coefficient(g, i) : i in [0..8]]);
		if newseq[2] eq 0 then // one point at infinity
			assert newseq[3] eq 0 and newseq[4] eq 0;
			s0 := 0; s1 := 1; s2 := newseq[6];
		else
			s0 := 1;
			s1 := newseq[3];	// sigma_1
			s2 := newseq[4];	// sigma_2
		end if;
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
		return -cof0/cof1;
	end if;
	if oldseq[2] eq 0 and oldseq[3] eq 0 and oldseq[4] eq 0 then
		y1y2_t2 := (oldseq[8] + 2*oldseq[6]^4*Coefficient(f, 8) - oldseq[6]^3*Coefficient(f, 7))/((-ti*oldseq[6] + ui)^4);
		if ti ne 0 then
			y1y2_t2 /:= ti;
		end if;
	else
		y1y2_t2 := ((oldseq[5] - 3*oldseq[4])*oldseq[8] + G_func(f, oldseq))/((ti^2*oldseq[4] - ti*ui*oldseq[3] + ui^2)^4);
	end if;
	if newseq[2] eq 0 and newseq[3] eq 0 and newseq[4] eq 0 then
		xi8 := y1y2_t2 - 2*newseq[6]^4*Coefficient(g, 8) + newseq[6]^3*Coefficient(g, 7);
	else
		xi8 := (y1y2_t2 - G_func(g,newseq))/(newseq[5] - 3*newseq[4]);
	end if;
	return xi8;
end function;

function KummerTransformation(C/*::CrvHyp*/, D/*::CrvHyp*/, mat/*::SeqEnum[RngElt]*/)// -> Map
/*{C, D: domain & codomain of transformation, mat := matrix in GL(2) representing the transformation.
 returns the descent on the Kummer Variety. }*/
	F := BaseRing(C);
	R<x> := PolynomialRing(F);
	_, _, ti, ui := Explode(Eltseq(Matrix(2,2,mat)^-1));
	r,s,t,u := Explode(mat);
	f, h := HyperellipticPolynomials(C);
	assert h eq 0;
	f0,f1,f2,f3,f4,f5,f6,f7,f8 := Explode([Coefficient(f, i) : i in [0..8]]);
	g, h := HyperellipticPolynomials(D);
	assert h eq 0;
	g0,g1,g2,g3,g4,g5,g6,g7,g8 := Explode([Coefficient(g, i) : i in [0..8]]);
	Sigma := Transpose(Matrix([ [Coefficient((r*x + s)^j * (t*x + u)^(4-j), i) : i in [0..4]]
															: j in [0..4]]));
	KC := KummerVarietyG3(C);
	KD := KummerVarietyG3(D);	
	mp := map<KC -> KD | P :-> 
						KD!Append(normalizetoaffine([F|xi1, mat[3,5], mat[2,5], mat[1,5], mat[4,2] + mat[1,5], mat[1,4], mat[1,3]]), xi8)
						where xi8 := (xi1 ne 0) select 
						mat[3,5]*mat[1,3] - mat[2,5]*mat[1,4] + mat[1,5]*(mat[4,2] + mat[1,5])
						else
						solveforxi8(f,g,normalizetoaffine(Eltseq(P)), newseq, ti, ui)
						where newseq := normalizetoaffine([F|0, mat[3,5], mat[2,5], mat[1,5], mat[4,2] + mat[1,5],
														mat[1,4], mat[1,3], 1])
						where xi1 := (mat[5,5] eq 0) select ((g7 eq 0) select 0 else mat[4,5]/g7) else mat[5,5]/(2*g8)
						
						where mat := Sigma*M*Transpose(Sigma)
						where	M := Matrix([[2*x1*f0,  		  x1*f1,     		   x7,        	 x6,    	 x4],
												       [	x1*f1, 2*(f2*x1-x7),  	 x1*f3-x6,     		x5-x4,    	 x3],
												       [  	 x7,     x1*f3-x6, 2*(x1*f4-x5),  	 x1*f5-x3,    	 x2],
												       [  	 x6,     		x5-x4,     x1*f5-x3, 2*(f6*x1-x2), 		x1*f7],
												       [     x4,        	 x3,        	 x2,       	x1*f7,  2*f8*x1]]) 
						where x1,x2,x3,x4,x5,x6,x7 := Explode(normalizetoaffine(Eltseq(P)))
						
				>;
	return mp;
end function;
