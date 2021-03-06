AttachSpec("spec");
Attach("torsion3.m");
Attach("transformations.m");

input := Open("gce_genus3_hyperelliptic.txt", "r");
output := Open("output.txt", "w");

S<x> := PolynomialRing(Rationals());

lc := 0;

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
	// print curve, basic properties
	fprintf output, line;
	fprintf output, ":[";
	i := 0;
	numofgens := #Generators(G);
	for g in Generators(G) do
		fprintf output, "%o", Order(g);
		i +:= 1;
		if i lt numofgens then
			fprintf output, ", ";
		end if;
	end for;
	fprintf output, "]\n";
	if lc mod 10 eq 0 then
		Flush(output);
	end if;
end while;


/*
input := Open("gce_genus3_hyperelliptic.txt", "r");
output := Open("output.txt", "w");

S<x> := PolynomialRing(Rationals());
C := SimplifiedModel(HyperellipticCurve(x^7 + 1));
J := Jacobian(C);
G, iso := myTorsionSubgroup(J);

fprintf output, "%o, %o: Rational Torsion generated by elements of order ", Discriminant(C), HyperellipticPolynomials(C);
for g in Generators(G) do
	fprintf output, "%o, ", Order(g);
end for;
fprintf output, "\n[";

i := 0;
for pt in G do
	fprintf output, "%o", iso(pt);
	i +:= 1;
	if i ne #G then
		fprintf output, ", ";
	end if;
end for;
fprintf output, "]\n";
*/
