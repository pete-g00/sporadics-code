G := SimpleGroup("O(7,3)");
S := SylowSubgroup(G, 3);
f := IsomorphismPcGroup(S);;
S := Image(f);

N := NormalSubgroups(S);;

OnImage := function(x, phi)
    return Image(phi, x);
end;

AutS := AutomorphismGroup(S);
M := Filtered(N, A -> Index(S,A) = 3);;
M := Orbits(AutS, M, OnImage);;

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(A_i)) \cong \SL_2(3)$
# -------------------------------------------------------------------------------------------------
A := First(M, A -> Size(A) = 3)[1]; # A has 3 $\Aut(S)$-conjugates
UA := UpperCentralSeries(A);

Z2A := UA[3];
T := Centralizer(A, Z2A);

Index(A, FrattiniSubgroup(A)); # should be 3^3

Index(A, T); # should be 3^2

Index(T, FrattiniSubgroup(A)); # should be 3

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(Q)) \cong \Alt(4)$ [TODO]
# -------------------------------------------------------------------------------------------------
Q := First(M, A -> Size(A) = 1 and Size(Center(A[1])) = 3)[1]; # Q unique characteristic so that $|Z(Q)| = 3$

Center(S) = Center(Q); # should be true

V := First(N, A -> Size(A) = 3^5 and IsElementaryAbelian(A));
W := First(N, A -> Size(A) = 3^7 and Rank(A) = 6);

FrattiniSubgroup(Q) = Intersection(V, W); # should be true
IsElementaryAbelian(FrattiniSubgroup(Q)); # true

Index(FrattiniSubgroup(Q), Center(S)); # 3^3
CommutatorSubgroup(S,V) = FrattiniSubgroup(Q); # true

AutQ := AutomorphismGroupPGroup(Q);;
AutQ.size mod 13; # 2

CommutatorSubgroup(Q, FrattiniSubgroup(Q)) = Center(Q); # true

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(R)) \cong \SL_2(3)$ 
# -------------------------------------------------------------------------------------------------
R := First(M, A -> Size(A) = 1 and Size(Center(A[1])) = 9)[1]; # R unique characteristic so that $|Z(Q)| = 9$

q := NaturalHomomorphismByNormalSubgroup(S,V);;
U := PreImage(q, Center(Image(q)));

Index(R, U); # $|R : U| = 3$
IsSubset(V, CommutatorSubgroup(S,U)); # $[S,U] \leq V$
Index(CommutatorSubgroup(R,V), Center(R)); # $|[R,V] : Z(R)| = 3$

UR := UpperCentralSeries(R);
Z2R := UR[2];

Z2R = FrattiniSubgroup(R); # $Z_2(R) = \Phi(R)$
Size(Z2R); IsElementaryAbelian(Z2R); # $Z_2(R)$ is elementary abelian of order $3^4$

Centralizer(S, Z2R) = Z2R; # $C_S(\Phi(R)) = \Phi(R)$

Size(Center(R)); # order $3^2$