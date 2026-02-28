G := SimpleGroup("O(7,3)");
S := SylowSubgroup(G, 3);
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
# The only subgroup of order $3^7$ of exponent $3$ is $3^{1+6}_+$
# -------------------------------------------------------------------------------------------------
Number(C, A -> Size(A) = 3^7 and Exponent(A) = 3); # should be 1

# -------------------------------------------------------------------------------------------------
# The only subgroup of order $3^7$ of exponent $3$ is $3^{1+6}_+$
# -------------------------------------------------------------------------------------------------
A := Filtered(C, IsElementaryAbelian);;
Maximum(List(A, Size)); # should be 3^5
Number(A, X -> Size(X) = 3^5); # should be 1

# -------------------------------------------------------------------------------------------------
# $\bfT_i = C_{A_i}(Z_2(A_i))$.
# -------------------------------------------------------------------------------------------------
W := First(C, A -> Size(A) = 3^7 and Exponent(A) = 3);
A := First(C, A -> Index(S,A) = 3 and Normalizer(G,A) <> G and IsSubset(A,W)); # A is not characteristic, maximal and contains $W$
T := First(C, A -> Size(A) = 3^6 and Normalizer(G,A) <> G and Rank(A) = 3 and Size(Center(A)) = 3^3); # T is not characteristic of shape $3^{3+3}$

UA := UpperCentralSeries(A);
Z2A := UA[3];
a := RepresentativeAction(G, T, Centralizer(A, Z2A)); # $\bfT_i$ and $C_{A_i}(Z_2(A_i))$ are $\Aut(S)$-conjugate
T := T^a; # now $T \leq A$

# -------------------------------------------------------------------------------------------------
# $|Aut(S) : N_{\Aut(S)}(A_i)| = 3$.
# -------------------------------------------------------------------------------------------------
Index(G, Normalizer(G,A)); # should be 3

# -------------------------------------------------------------------------------------------------
# $Z_2(S) = Z(R) \leq Z_2(A_i) = Z(T_i) \leq Z_2(R) = Z_3(S)$
# -------------------------------------------------------------------------------------------------
U := UpperCentralSeries(S);
Z2S := U[4];
Z3S := U[3];

R := Centralizer(S, Z2S); # $R = C_S(Z_2(S))$
UR := UpperCentralSeries(R);
Z2R := UR[2];

Z2A := Center(T); # $Z_2(A_i) = Z(T_i)$
Z2R = Z3S; # $Z_2(R) = Z_3(S)$
IsSubset(Z2A, Z2S); # $Z_2(S) \leq Z_2(A_i)$
IsSubset(Z3S, Z2A); # $Z_2(A_i) \leq Z_3(S)$
