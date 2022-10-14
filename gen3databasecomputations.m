AttachSpec("spec");
Attach("torsion3.m");
Attach("transformations.m");

input := Open("gce_genus3_hyperelliptic.txt", "r");
output := Open("output.txt", "w");

S<x> := PolynomialRing(Rationals());

lc := 0;

groups := [];
curves := [];

while true do
	lc +:= 1;
	print lc;
	line :=  Gets(input);
	if IsEof(line) then
		break;
	end if;
	pols := Split(line, "[]")[2];
	seppols := Split(pols, ",");
	f, h := Explode([eval seppols[1], eval seppols[2]]);
	C := SimplifiedModel(HyperellipticCurve(f, h));
	J := Jacobian(C);
	G:= myTorsionSubgroup(J);
        invs := InvariantFactors(G);
        ind := Index(groups, invs);
        f := HyperellipticPolynomials(C);
        if invs notin groups then
          Append(~groups, invs);
          Append(~curves, [f]);
        else 
          Append(~curves[ind], f);
        end if;
	// print curve, basic properties
	fprintf output, line;
	fprintf output, ":[";
	i := 0;
        fprintf output, "%o", invs;
	fprintf output, "]\n";
	if lc mod 100 eq 0 then
		Flush(output);
	end if;
end while;

curves_count := [#c : c in curves];

load "howe_zhu.m";
simple := [];
only_simple := [];
split := [];
only_split := [];
for i := 1 to #groups do
  "group", groups[i];
  simple_found := false;
  split_found := false;
  j := 1;
  repeat 
    f := curves[i,j];
    b := HasAbsolutelyIrreducibleJacobian(HyperellipticCurve(f), 50);
    if b and not simple_found then
      Append(~simple, groups[i]);
      simple_found := true;
    elif not b and not split_found then
      Append(~split, groups[i]);
      split_found := true;
    end if;
    j +:= 1;
  until (split_found and simple_found) or j gt #curves[i];
  if not simple_found then 
    Append(~only_split, groups[i]);
  end if;
  if not split_found then 
    Append(~only_simple, groups[i]);
  end if;
end for;
      



fprintf output, " //groups: \n groups := %o\n\n", groups;
fprintf output, " //curves: \n curves := %o\n\n", curves;
fprintf output, " //numbers of curves: \n curves_count := %o\n\n", curves_count;
fprintf output, " //group structures showing up for geometrically simple Jacobians: \n simple := %o\n\n", simple;
fprintf output, " //group structures showing up for Jacobians that are not known to be geometrically simple: \n probably_split := %o\n\n", split;
fprintf output, " //group structures showing up only for geometrically simple Jacobians: \n only_simple := %o\n\n", only_simple;
fprintf output, "//group structures showing up only for Jacobians that are not known to be geometrically simple: \n only_probably_split := %o\n\n", only_split;
