/* Computes different polynomials associated to the Kummer Variety of a curve C. Mainly uses
	G3HypHelp.m for this.
	KummerBB: Computes Biquadratic forms associated with C.
	KummerD: Computes KummerDeltas (Doubling polynomials) associated with C.
*/

Attach("G3HypHelp.m");
import "G3HypHelp.m": K3quartics, K3deltas, Xipolynomials, K3biquforms, K3xi2coeffs;

// We store the data with the curve

declare attributes CrvHyp:
 KummerEquations, KummerVariety, KummerDeltas, KummerXipols, KummerBQF, HeightTable;

declare verbose ReducedBasis, 2;

declare verbose FindPointsG3, 3;

function kummerBB(C)
    if assigned C`KummerBQF then
        BB := C`KummerBQF;
    else
        f := HyperellipticPolynomials(C);
        fs := Coefficients(f);
        fs cat:= [0 : i in [#fs+1..9]];
        BB := K3biquforms(fs);
        C`KummerBQF := BB;
    end if;
    return BB;
end function;

function kummerD(C)
    if assigned C`KummerDeltas then
        deltas := C`KummerDeltas;
        R := Universe(deltas);
    else
        f := HyperellipticPolynomials(C);
        fs := Coefficients(f);
        fs cat:= [0 : i in [#fs+1..9]];
        R := assigned C`KummerEquations
            select Universe(C`KummerEquations)
            else PolynomialRing(Universe(fs), 8);
        deltas := K3deltas(fs : Ring := R);
        C`KummerDeltas := deltas;
    end if;
    return deltas;
end function;
