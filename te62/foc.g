# -------------------------------------------------------------------------------------------------
# $[S, A \cap R] \nleq \Phi(R)$
# -------------------------------------------------------------------------------------------------

S := PcGroupCode(
13741491938431806455657762112574406588684703498867453558824558564013195548929578751329924342130079075234146575466397002123106897939463680, 3^10);
U := UpperCentralSeries(S);
R := Centralizer(S, U[5]);

W := First(CharacteristicSubgroups(S), A -> Rank(A) = 6 and Size(A) = 3^7 and Exponent(A) = 3);
q := NaturalHomomorphismByNormalSubgroup(S, W);;
M := MaximalSubgroups(Image(q));
M := List(M, A -> PreImage(q, A));

M := Filtered(M, A -> not IsCharacteristicSubgroup(S,A));

A := M[1];

C := CommutatorSubgroup(S, Intersection(A,R));

IsSubset(FrattiniSubgroup(R), C); # false
