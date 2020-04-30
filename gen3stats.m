input := Open("database.txt", "r");

lc := 0;

trivialtorsioncount := 0;
oddtorsioncount := 0;
biggesttorsion := 0;
biggesttorsionline := "";
largestorderelt := 0;
largestordereltline := "";
largestprimeorder := 0;
largestprimeorderline := "";


while true do
	lc +:= 1;
	line :=  Gets(input);
	if IsEof(line) then
		break;
	end if;
	gens := (#Split(line, "[]") eq 4) select Split(line, "[]")[4] else [];
	sepgens := (#gens eq 0) select [] else Split(gens, ",");
	// counters
	if #sepgens eq 0 then
		trivialtorsioncount +:= 1;
	end if;
	for g in sepgens do
		if #Factorization(eval g) ge 2 or Factorization(eval g)[1][1] ne 2 then
			oddtorsioncount +:= 1;
			break;
		end if;
	end for;
	m := 1;
	// highlight curves
	for g in sepgens do
		m *:= (eval g);
		if m ge biggesttorsion then
			biggesttorsion := m;
			biggesttorsionline := line;
		end if;
		if (eval g) ge largestorderelt then
			largestorderelt := (eval g);
			largestordereltline := line;
		end if;
		fact := Factorization(eval g);
		if fact[#fact][1] ge largestprimeorder then
			largestprimeorder := fact[#fact][1];
			largestprimeorderline := line;
		end if;
	end for;
end while;
