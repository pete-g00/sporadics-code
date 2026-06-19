LoadPackage("ANUPQ"); # for isomorphism of $p$-groups

G := SimpleGroup("Suz");
S := SylowSubgroup(G, 3);
f := IsomorphismPcGroup(S);;
S := Image(f);

# -------------------------------------------------------------------------------------------------
# As a group, $S$ is indecomposable
# -------------------------------------------------------------------------------------------------
Length(DirectFactorsOfGroup(S)); # should be 1

# -------------------------------------------------------------------------------------------------
# A Sylow $3$-subgroup of $\Sp_2(3) \circ \SO_6^+(3)$ is not isomorphic to $S$
# -------------------------------------------------------------------------------------------------
A := DirectProduct(Sp(IsPermGroup, 2, 3), SO(IsPermGroup, +1, 6, 3));
Zed := Center(A);
M := MaximalSubgroups(Zed);
A := List(M, X -> A/X);
A3 := List(A, X -> SylowSubgroup(X, 3));
f := List(A3, IsomorphismPcGroup);;
A3 := List(f, Image);
ForAll(A3, X -> not IsIsomorphicPGroup(X, S)); # should be true

# -------------------------------------------------------------------------------------------------
# A Sylow $3$-subgroup of $\Sp_2(3) \circ \SO_6^-(3)$ is not isomorphic to $S$
# -------------------------------------------------------------------------------------------------
A := DirectProduct(Sp(IsPermGroup, 2, 3), SO(IsPermGroup, -1, 6, 3));
Zed := Center(A);
M := MaximalSubgroups(Zed);
A := List(M, X -> A/X);
A3 := List(A, X -> SylowSubgroup(X, 3));
f := List(A3, IsomorphismPcGroup);;
A3 := List(f, Image);
ForAll(A3, X -> not IsIsomorphicPGroup(X, S)); # should be true
