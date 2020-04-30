/* Creation function for the Kummer Variety of a curve:
	KummerVarietyG3: Creates the Kummer Variety associated with the given Hyperelliptic Curve C,
	in the given Ambient. If Ambient is not set, the Kummer Variety will be over the same field C
	is defined over.*/

Attach("G3HypHelp.m");
import "G3HypHelp.m": K3quartics, K3deltas, Xipolynomials, K3biquforms, K3xi2coeffs;

// We store the data with the curve

declare attributes CrvHyp:
 KummerEquations, KummerVariety, KummerDeltas, KummerXipols, KummerBQF, HeightTable;

intrinsic KummerVarietyG3(C::CrvHyp : Ambient := "") -> Sch
{Construct the Kummer variety associated to the genus 3 hyperelliptic curve C.
 If Ambient is not set, it will create the Kummer Variety over the field C is defined over.}
	// For now, the attribute C`KummerVariety is only set over the field C is defined over.
  if assigned C`KummerVariety and Ambient cmpeq "" then
    return C`KummerVariety;
  elif assigned C`KummerEquations then
    if Ambient cmpeq "" then
      Ambient := ProjectiveSpace(Universe(C`KummerEquations));
    end if;
    K := Scheme(Ambient, C`KummerEquations);
    if Ambient cmpeq "" then
      C`KummerVariety := K;
    end if;
    return K;
  else // if Kummer equations still have to be created.
    	// create ambient, basic condition checks.
    if Ambient cmpeq "" then
	    Ambient := ProjectiveSpace(BaseRing(C), 7);
    end if;
    require Genus(C) eq 3: "The curve must be of genus 3.";
    f, h := HyperellipticPolynomials(C);
    require h eq 0: "The curve must have the form y^2 = f(x).";
    
    	// create list of coeffs.
    fs := Coefficients(PolynomialRing(CoordinateRing(Ambient)) ! f);
    fs cat:= [0 : i in [#fs+1..9]];
    	// K is defined by 34 quartics, 1 quadric, see [4], section 3.
    quartics := K3quartics(fs : Ring := CoordinateRing(Ambient));
    quad := P.1*P.8 - P.2*P.7 + P.3*P.6 - P.4*P.5 where P := Universe(quartics);
    KEquations := [quad] cat quartics;
    K := Scheme(Ambient, KEquations);
    if BaseRing(Ambient) cmpeq BaseRing(C) then
      C`KummerVariety := K;
      C`KummerEquations := KEquations;
    end if;
    return K;
  end if;
end intrinsic;
