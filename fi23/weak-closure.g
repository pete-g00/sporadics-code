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

M := MaximalSubgroups(S);
M := Filtered(M, A -> Index(S,A) = 3 and IsNormal(G,A));;

US := UpperCentralSeries(S);
Z2S := US[8];
Z3S := US[7];
Z5S := US[5];

Q := First(M, A -> Agemo(A,3) = Z5S);
R := Centralizer(S, Z2S);
P := First(M, A -> not A in [Q,R]);

C := SubgroupsSolvableGroup(G, rec(series := DerivedSeries(S), groups := [S]));;

# -------------------------------------------------------------------------------------------------
# The only subgroup of order $3^7$ of exponent $3$, rank $8$ is $3^{1+8}_+$
# -------------------------------------------------------------------------------------------------
Number(C, A -> Size(A) = 3^9 and Rank(A) = 8 and Exponent(A) = 3); # should be 1

# -------------------------------------------------------------------------------------------------
# The maximal elementary abelian subgroups of $S$ have order $3^6$, and $J(S) = Q \cap R$
# -------------------------------------------------------------------------------------------------
A := Filtered(C, IsElementaryAbelian);;
Maximum(List(A, Size)); # should be 3^6
A := Filtered(C, A -> Size(A) = 3^6);

J := ClosureGroup(A[1], ClosureGroup(A[2], A[3]));

J = Intersection(Q, R);

# -------------------------------------------------------------------------------------------------
# Structure of $U$
# -------------------------------------------------------------------------------------------------

U := Centralizer(S, Z3S);

UP := UpperCentralSeries(P);
UR := UpperCentralSeries(R);

Z2P := UP[5];
Z2R := UR[6];

U = Centralizer(P, Z2P);
U = Centralizer(R, Z2R);
