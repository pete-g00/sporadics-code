# -------------------------------------------------------------------------------------------------
# $[S, Q \cap R] \nleq \Phi(R)$
# -------------------------------------------------------------------------------------------------

G := SimpleGroup("Fi23");
S := SylowSubgroup(G, 3);
f := IsomorphismPcGroup(S);;
S := Image(f);

AutS := AutomorphismGroupPGroup(S);;
AutS_PC := PcGroupAutPGroup(AutS);
AutS := ConvertHybridAutGroup(AutS);

t := GroupHomomorphismByImagesNC(AutS_PC, AutS);;
G := SplitExtension(AutS_PC, t, S);
S := ModuleOfExtension(G);

U := UpperCentralSeries(S);;
R := Centralizer(S, U[8]);

W := First(CharacteristicSubgroups(S), A -> Exponent(A) = 3 and Rank(A) = 8);

q := NaturalHomomorphismByNormalSubgroup(S, W);;

Q := First(MaximalSubgroups(Image(q)), IsElementaryAbelian);
Q := PreImage(q, Q);

C := CommutatorSubgroup(S, Intersection(Q,R));

IsSubset(FrattiniSubgroup(R), C); # false
