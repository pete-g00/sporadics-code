G := SimpleGroup("O(+1,8,3)");
S := SylowSubgroup(G, 3);

M := MaximalSubgroups(S);;

NGM := List(M, A -> Normalizer(G,A));;

I := Filtered([1..Length(M)], i -> PCore(NGM[i],3) = M[i]);

M := M{I};;
NGM := NGM{I};;

i := PositionProperty(M, A -> Center(A) <> Center(S));

R := M[i];
NGR := NGM[i];

I := PositionsProperty(M, A -> Center(A) = Center(S));

Ex := M{I};
NGX := NGM{I};

NGT := List(NGX, A -> ClosureGroup(A, NGR));
T := List(NGT, A -> PCore(A,3));

NGU := List([1..2], i -> ClosureGroup(NGX[i], NGX[i+1]));
Add(NGU, ClosureGroup(NGX[3], NGX[1]));
U := List(NGU, X -> PCore(X,3));

V := List(NGU, A -> ClosureGroup(NGR,A));
NGV := List(NGU, A -> ClosureGroup(NGR,A));
V := List(NGV, A -> PCore(A,3));

NGW := ClosureGroup(NGX[1], ClosureGroup(NGX[2], NGX[3]));
W := PCore(NGW,3);

f := IsomorphismPcGroup(S);;
S := Image(f);

R := Image(f, R);
Ex := List(Ex, X -> Image(f,X));

T := List(T, A -> Image(f,A));
U := List(U, A -> Image(f,A));
V := List(V, A -> Image(f,A));

W := Image(f,W);

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(X_i)) \cong \SL_2(3) 
# -------------------------------------------------------------------------------------------------
List(Ex, X -> Index(X, FrattiniSubgroup(X)); # index 3^4 in each case
ForAll([1..3], i -> CommutatorSubgroup(S, T[i]) = FrattiniSubgroup(Ex[i])); # should be true
List([1..3], i -> Index(Ex[i], T[i])); # should be 3^2 in each case

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(R)) \cong \SL_2(3) 
# -------------------------------------------------------------------------------------------------

FR := FrattiniSubgroup(R);
FR = Intersection(T); # should be true
Centralizer(S, FR) = FR; # should be true

US := UpperCentralSeries(S);
Z3S := US[3]; 
Z3S = FR; # should be true

FR = CommutatorSubgroup(CommutatorSubgroup(R,S), S);

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(T_i)) \cong \SL_3(3) 
# -------------------------------------------------------------------------------------------------

# $V_i \cap V_{i+1} = Z(T_{i+1})$
Intersection(V[1], V[2]) = Center(T[2]); # should be true
Intersection(V[2], V[3]) = Center(T[3]); # should be true
Intersection(V[3], V[1]) = Center(T[1]); # should be true

List([1..3], i -> Index(V[i], Center(T[i]))); # should be 3 in each case

ForAll([1..3], i -> IsSubset(Center(T[i]), CommutatorSubgroup(V[i], T[i]))); # should be true

ForAll(V, A -> Centralizer(S,A) = A);  # should be true

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(U_i)) \cong O^+_4(3) 
# -------------------------------------------------------------------------------------------------

List(U, A -> Index(A, FrattiniSubgroup(A))); # should be 3^5 in each case
ForAll([1..3], i -> Centralizer(S, FrattiniSubgroup(U[i])) = V[i]); # should be true, i.e. $C_S(\Phi(U_i)) = V_i$
