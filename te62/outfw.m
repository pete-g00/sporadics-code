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
U := [A : A in U | <3,3> in FactoredOrder(A) and IdentifyGroup(Sylow(A,3)) eq <3^3,3> and pResidue(A,3) eq A and IsIrreducible(Restriction(V, A))];
#U; // should equal 1
U := U[1];

S := Sylow(U,3);
T := Subgroups(S);
T := [A`subgroup : A in T | #A`subgroup in [3,9]];

NGT := [Normalizer(U,A) : A in T];
I := [i : i in [1..#T] | pCore(NGT[i],3) eq T[i]];

#I; // should equal 5, i.e. essentials in $N_F(W)$ are: $Q$, $Y$ and the three conjugates $X_i$
