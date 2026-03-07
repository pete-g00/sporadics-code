G := SimpleGroup("Fi23");
S := SylowSubgroup(G, 3);
f := IsomorphismPcGroup(S);;
S := Image(f);

M := MaximalSubgroups(S);
M := Filtered(M, A -> Index(S,A) = 3 and IsCharacteristicSubgroup(S,A));;

US := UpperCentralSeries(S);
Z2S := US[8];
Z3S := US[7];
Z5S := US[5];

Q := First(M, A -> Agemo(A,3) = Z5S);
R := Centralizer(S, Z2S);
P := First(M, A -> not A in [Q,R]);

W := First(CharacteristicSubgroups(S), A -> Rank(A) = 8 and Size(A) = 3^9 and Exponent(A) = 3);
J := Intersection(Q,R);
U := Centralizer(S, Z3S);

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(P)) \cong \SL_2(3)$
# -------------------------------------------------------------------------------------------------
UP := UpperCentralSeries(P);

Z5P := UP[2];
Z4P := UP[3];

FrattiniSubgroup(P) = Z5P; # should be true

Index(P, FrattiniSubgroup(P)); # should be 3^4

Index(ClosureGroup(W, FrattiniSubgroup(P)), W); # should be 3

Index(CommutatorSubgroup(P,W), Z4P); # should be 3

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(Q)) \cong \Alt(4)$
# -------------------------------------------------------------------------------------------------
Index(Q, FrattiniSubgroup(Q)); # should be 3^4
AutQ := AutomorphismGroupPGroup(Q);;
AutQ.size mod 13; # should be nonzero

UJ := UpperCentralSeries(J);
Z2J := UJ[2];

Z2J = Centralizer(S, Z2J); # should be true

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(R)) \cong \SL_2(3)$
# -------------------------------------------------------------------------------------------------
UR := UpperCentralSeries(R);
Z4R := UR[4];
Z3R := UR[5];
Z2R := UR[6];
ZR := UR[7];

FrattiniSubgroup(R) = CommutatorSubgroup(S, U); # should be true
IsElementaryAbelian(Z4R); # should be true
Size(Z4R); # order 3^5

Index(Z4R, Z3R); # should be 3
Index(Z3R, Z2R); # should be 3
Index(Z2R, ZR); # should be 3

Centralizer(R, Z4R) = Z4R; # should be true
