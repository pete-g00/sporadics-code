G := PSU(5,2);
S := Sylow(G,3);

C := Subgroups(S);
C := [A`subgroup : A in C];
C := [A : A in C | Centralizer(G,A) eq Center(A) and pCore(Normalizer(G,A),3) eq A]; // centric, radical in $F_S(G)$
#C; // 3

[GroupName(A) : A in C]; // has: $3^4$, $3*3^{1+2}_+$ and $S$ (note essentials in $N_F(W)$ can only be the first two subgroups)

Q := [A : A in C | IsAbelian(A)][1];
GroupName(Normalizer(G,Q)/Q); // $\Sym(5)$

GroupName(Normalizer(G,S)/S); // $2^2$
