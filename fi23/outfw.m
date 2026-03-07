pResidue := function(G,p)
    return NormalClosure(G, Sylow(G,p));
end function;

G := Sp(8,3);

M  := MaximalSubgroups(G : OrderEqual := 3317760);

M := M[1]`subgroup;

I := Subgroups(M : OrderMultipleOf := 3^4);
I := [A`subgroup : A in I];
I := [A : A in I | #pCore(A,3) eq 1 and pResidue(A,3) eq A];
#I; // should be 4

S := [Sylow(A, 3) : A in I];

C := [Subgroups(A) : A in S];
C := [[A`subgroup : A in X] : X in C];
C := [[A : A in C[i] | Index(Normalizer(S[i],A), A) eq 3] : i in [1..#C]];

P := [[A : A in C[i] | Index(S[i],A) eq 3 and Exponent(A) eq 3 and NilpotencyClass(A) eq 2][1] : i in [1..#C]];
Q := [[A : A in C[i] | Index(S[i],A) eq 3 and IsElementaryAbelian(A)][1] : i in [1..#C]];

// find the ones that are essential in each case

D := [[A : A in C[i] | pCore(Normalizer(I[i], A),3) eq A] : i in [1..#C]];

[i : i in [1..#D] | P[i] in D[i]]; // P essential in [ 3, 4 ]
[i : i in [1..#D] | Q[i] in D[i]]; // Q essential in [ 2, 4 ]
[i : i in [1..#D] | 9 in [#A : A in D[i]]]; // X essential in [ 1, 2, 3, 4 ]
[i : i in [1..#D] | 3 in [#A : A in D[i]]]; // Y essential in [ 1, 2 ]

[GroupName(pCore(A/pCore(A,2),3)) : A in I]; // $3 \wr 3$, $3^3$, $3^{1+2}_+$, $1$
