AttachSpec("spec");
Attach("torsion3.m");
Attach("transformations.m");

input := Open("gce_genus3_hyperelliptic.txt", "r");
output := Open("output.txt", "w");

S<x> := PolynomialRing(Rationals());

lc := 0;

groups := [];
curves := [];
bigger100 := [];
bigger1000 := [];

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
        f := HyperellipticPolynomials(C);
        bad := BadPrimes(C);
        nprimes := #[p : p in PrimesInInterval(2,100) | p notin bad];
	J := Jacobian(C);
        tb := myTorsionBound(J, nprimes);
	G := myTorsionSubgroup(J);
        invs := InvariantFactors(G);
        if #G lt tb then
          Append(~bigger100, <f, tb, #G, invs>);
        end if;
        ind := Index(groups, invs);
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
      


fprintf output, " //groups: \n groups := %o;\n\n", groups;
fprintf output, " //curves: \n curves := %o;\n\n", curves;
fprintf output, " //numbers of curves: \n curves_count := %o;\n\n", curves_count;
fprintf output, " //group structures showing up for geometrically simple Jacobians: \n simple := %o;\n\n", simple;
fprintf output, " //group structures showing up for Jacobians that are not known to be geometrically simple: \n probably_split := %o;\n\n", split;
fprintf output, " //group structures showing up only for geometrically simple Jacobians: \n only_simple := %o;\n\n", only_simple;
fprintf output, "//group structures showing up only for Jacobians that are not known to be geometrically simple: \n only_probably_split := %o;\n\n", only_split;
fprintf output, " //curves with torsion order smaller than the upper bound obtained from considering good primes below 100: \n bigger100 := %o;\n\n", bigger100;

for i in [1..#bigger100] do 
"i", i;
  t := bigger100[i];
  f := t[1];
  C := HyperellipticCurve(f);
  bad := BadPrimes(C);
  nprimes := #[p : p in PrimesInInterval(2,1000) | p notin bad];
  tb := myTorsionBound(Jacobian(C), nprimes);
  if tb lt t[2] then 
    bigger100[i,2] := tb;
  end if;
end for;

for i in [1..#bigger100] do
  t := bigger100[i];
  if t[3] ne t[2] then
    Append(~bigger1000, t);
  end if;
end for;


fprintf output, " //curves with torsion order smaller than the upper bound obtained from considering good primes below 1000: \n bigger1000 := %o;\n\n", bigger1000;

quots := [t[2]/t[3] : t in bigger1000];
L := [];
M := [];
N := [];
O := [];
load "howe_zhu.m";

for q in Sort(SetToSequence(SequenceToSet(quots))) do
  Append(~L, <q, #[r : r in quots | r eq q]>);
  ts := [t : t in bigger1000 | t[2]/t[3] eq q];
  Append(~M, <q, ts >);
  nauts := [#AutomorphismGroup(HyperellipticCurve(t[1])) : t in ts];
  Append(~N, <q, nauts>);
  simple := [];
  for i in [1..#ts] do
    if nauts[i] ne 2 then
      Append(~simple, false);
    else
      f := ts[i,1];
      Append(~simple, HasAbsolutelyIrreducibleJacobian(HyperellipticCurve(f), 50));
    end if;
  end for;
  Append(~O, <q, simple>);
end for;

