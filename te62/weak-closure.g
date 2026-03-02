S := PcGroupCode(
13741491938431806455657762112574406588684703498867453558824558564013195548929578751329924342130079075234146575466397002123106897939463680, 3^10);

AutS := AutomorphismGroupPGroup(S);;
AutS_PC := PcGroupAutPGroup(AutS);
AutS := ConvertHybridAutGroup(AutS);
t := GroupHomomorphismByImagesNC(AutS_PC, AutS);;

G := SplitExtension(AutS_PC, t, S);
S := ModuleOfExtension(G);

C := SubgroupsSolvableGroup(G, rec(series := DerivedSeries(S), groups := [S]));;

# -------------------------------------------------------------------------------------------------
# The only subgroup of order $3^7$ of exponent $3$, rank $6$ is $3^{1+6}_+$
# -------------------------------------------------------------------------------------------------
Number(C, A -> Size(A) = 3^7 and Exponent(A) = 3 and Rank(A) = 6); # should be 1


# The only subgroup of order $3^7$ of exponent $3$ is $3^{1+6}_+$
# -------------------------------------------------------------------------------------------------
Number(C, A -> Size(A) = 3^7 and Exponent(A) = 3); # should be 1

# -------------------------------------------------------------------------------------------------
# The maximal elementary abelian subgroups of $S$ have order $3^6$, and there is only one such group.
# -------------------------------------------------------------------------------------------------
A := Filtered(C, IsElementaryAbelian);;
Maximum(List(A, Size)); # should be 3^6
Number(A, X -> Size(X) = 3^6); # should be 1
