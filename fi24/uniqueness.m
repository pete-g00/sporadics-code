// Aut_F(R) determines Aut_F(V). Note that $R/V$ is not equal to $C_{S/V}(Z_2(S/V))$.

pResidue := function(G,p)
return NormalClosure(G, Sylow(G,p));
end function;

G := SO(7,3);
U := GL(7,3);
V := GModule(G);
S := Sylow(G, 3);
M := MaximalSubgroups(S);
M := [A`subgroup : A in M];
M := [A : A in M | #Center(A) eq 3 and Index(pResidue(Normalizer(G,A), 3), A) eq 24]; // R is essential containing W and supporting SL_2(3)
R := M[1];
NGR := Normalizer(G, R);
Index(Normalizer(U,NGP), NGR); // 2
CohomologicalDimension(Restriction(V, NGR), 1); // 0
