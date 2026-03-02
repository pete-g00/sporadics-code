G := SimpleGroup("O(+1,8,3)");

S := SylowSubgroup(G,3);
f := IsomorphismPcGroup(S);;
S := Image(f);

AutS := AutomorphismGroupPGroup(S);;
AutS_PC := PcGroupAutPGroup(AutS);
AutS := ConvertHybridAutGroup(AutS);
t := GroupHomomorphismByImagesNC(AutS_PC, AutS);;

G := SplitExtension(AutS_PC, t, S);
S := ModuleOfExtension(G);

C := SubgroupsSolvableGroup(G, rec(series := DerivedSeries(S), groups := [S]));;

# -------------------------------------------------------------------------------------------------
# The only subgroup of order $3^9$ of exponent $3$ is $3^{1+8}_+$
# -------------------------------------------------------------------------------------------------
Number(C, A -> Size(A) = 3^9 and Exponent(A) = 3); # should be 1

