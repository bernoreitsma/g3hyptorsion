// Given a curve over the rationals, check whether its Jacobian is absolutely irreducible
//
function has_abs_irred_jac_fin_g2(C : printlevel := 0)
  // C is a curve defined over a finite field F_q
  // Check if the Jacobian of C is absolutely irreducible, using Theorem 6 of
  // Howe-Zhu "On the existence of absolutely simple abelian varieties
  // of a given dimension over an arbitrary field"
  Fq := BaseRing(C);
  g := Genus(C);
  Z := ZetaFunction(C);
  f := Reverse(Numerator(Z)); // Weil poly
  pl := printlevel;
  if not IsIrreducible(f) then 
    if pl gt 0 then  printf "Reducible over %o\n", Fq; end if;
    return false; 
  end if;
  q := #Fq;
  a := Coefficient(f, 3);
  b := Coefficient(f, 2);
  if a ne 0 and a^2 ne q+b and a^2 ne 2*b and a^2 ne 3*b-3*q then
    return true;
  else 
    return false;
  end if;
end function;

function has_abs_irred_jac_fin(C : printlevel := 0)
  // C is defined over a finite field F_q
  // Check if the Jacobian of C is absolutely irreducible, using Proposition 3 of
  // Howe-Zhu "On the existence of absolutely simple abelian varieties
  // of a given dimension over an arbitrary field"
  // See Lemma 3.1 of Smith "Families of explicit isogenies of hyperelliptic Jacobians"
  Fq := BaseRing(C);
  g := Genus(C);
  Z := ZetaFunction(C);
  f := Reverse(Numerator(Z));
  pl := printlevel;
  if not IsIrreducible(f) then 
    if pl gt 0 then  printf "Reducible over %o\n", Fq; end if;
    return false; 
  end if;
  pl := printlevel;
  K<pi> := NumberField(f); 
  // phi(n) \ge sqrt(n)/sqrt(2)
  // d in D => phi(d) | 2g
  D := [d : d in [2..8*g^2] | IsDivisibleBy(2*g, EulerPhi(d))];
  for d in D do
    if &and[IsZero(Coefficient(f, n)) : n in [0..2*g] | n mod d ne 0] then
      if pl gt 0 then  printf "(1) happening \n"; end if;
      return false;
    else 
      L := sub< K | pi^d>; 
      if Degree(L) lt Degree(K) then
        rts := Roots(ChangeRing(CyclotomicPolynomial(d), K));
        if not IsEmpty(rts) then
          for rt in [t[1] : t in rts] do
            M := sub<K | [pi^d, rt]>;
            if IsIsomorphic(K, M) then
              if pl gt 1 then  printf "(2) happening\n"; end if;
              return false;
            end if;
          end for;
        end if;
      end if;
    end if;
  end for;
  return true;
end function;


function HasAbsolutelyIrreducibleJacobian(C, bound : printlevel := 0)
  // C is defined over Q 
  // Check if the Jacobian of C is absolutely irreducible, by checking if its reduction 
  // mod some prime of good reduction is absolutely irreducible.
  // Try all primes below bound.
  p := 2;
  g := Genus(C);
  pl := printlevel;
  while p lt bound do
    Cp := ChangeRing(C, GF(p));
    if not IsSingular(Cp) and not HasSingularPointsOverExtension(Cp) then
    /*
      if g eq 2 then 
        if is_good_ordinary(C, p) then
          if pl gt 0 then printf "Trying prime %o\n", p; end if;
          //if has_abs_irred_jac_fin_g2(Cp : printlevel := pl) then return true, p; end if;
        end if;
      else 
      */
      if pl gt 0 then printf "Trying prime %o\n", p; end if;
      if has_abs_irred_jac_fin(Cp : printlevel := pl) then return true, p; end if;
    end if;
    p := NextPrime(p);
  end while;
  return false, 0; // This doesn't mean that the Jacobian isn't absolutely irreducible!
end function;

