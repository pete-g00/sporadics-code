// Aut_F(P) determines Aut_F(V)

pResidue := function(G,p)
return NormalClosure(G, Sylow(G,p));
end function;

G := SO(7,3);
U := GL(7,3);
V := GModule(G);
S := Sylow(G, 3);
M := MaximalSubgroups(S);
M := [A`subgroup : A in M];
M := [A : A in M | #Center(A) eq 3 and Index(pResidue(Normalizer(G,A), 3), A) eq 24]; // P is essential containing W and supporting SL_2(3)
P := M[1];
NGP := Normalizer(G, P);
Index(Normalizer(U,NGP), NGP); // 2
CohomologicalDimension(Restriction(V, NGP), 1); // 0
