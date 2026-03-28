# -------------------------------------------------------------------------------------------------
# $[S, A \cap R] \nleq \Phi(R)$
# -------------------------------------------------------------------------------------------------

S := PcGroupCode(
13741491938431806455657762112574406588684703498867453558824558564013195548929578751329924342130079075234146575466397002123106897939463680, 3^10);

AutS := AutomorphismGroupPGroup(S);;
AutS_PC := PcGroupAutPGroup(AutS);
AutS := ConvertHybridAutGroup(AutS);

t := GroupHomomorphismByImagesNC(AutS_PC, AutS);;
G := SplitExtension(AutS_PC, t, S);
S := ModuleOfExtension(G);

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

# -------------------------------------------------------------------------------------------------
# If $B \in \Syl_2(\Aut(S))$, then $C := C_B(S/Q)$ has order $2^2$ and satisfies $[S, C] = Q$.
# -------------------------------------------------------------------------------------------------
B := SylowSubgroup(G, 2);
B := ClosureGroup(S, B);

C := StepCentralizer(B, S, A);
PValuation(Size(C),2); # 2
CommutatorSubgroup(S, C) = A; # true

