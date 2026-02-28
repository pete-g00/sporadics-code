// Computes $O^{p'}(G)$
pResidue := function(G,p)
    return NormalClosure(G, Sylow(G,p));
end function;

G := Sp(6,3);
V := GModule(G);

M := MaximalSubgroups(G);
M := [A`subgroup : A in M | #pCore(A`subgroup, 2) eq 2^9][1];

U := Subgroups(M : OrderMultipleOf := 3^2);
U := [A`subgroup : A in U];
U := [A : A in U | <3,2> in FactoredOrder(A) and IsElementaryAbelian(Sylow(A,3)) and pResidue(A,3) eq A and IsIrreducible(Restriction(V, A))];
#U; // should equal 3

S := [Sylow(A,3) : A in U];
MS := [MaximalSubgroups(A) : A in S];
MS := [[X`subgroup : X in A] : A in MS];

NMS := [[Normalizer(U[i],X) : X in MS[i]] : i in [1..#MS]];
NMS := [[NMS[i][j] :  j in [1..#MS[i]] | pCore(NMS[i][j],3) eq MS[i][j]] : i in [1..#MS]];

[GroupName(A/pCore(A,3)) : A in NMS[1]]; // $\SL_2(3), 2*\Alt(4)$
[GroupName(A/pCore(A,3)) : A in NMS[2]]; // $\SL_2(3)$, $\SL_2(3)$, $2*\Alt(4)$
[GroupName(A/pCore(A,3)) : A in NMS[3]]; // $\SL_2(3)$, $\SL_2(3)$, $\SL_2(3)$, $2*\Alt(4)$
