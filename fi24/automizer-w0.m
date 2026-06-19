G := SL(5,3);

M := MaximalSubgroups(G : OrderMultipleOf := 3^4);
M := [A`subgroup : A in M];

Q := [Sylow(A,3)/pCore(A,3) : A in M];

I := [i : i in [1..#Q] | #Q[i] gt 3^4 or IdentifyGroup(Q[i]) eq <3^4,7>];

M := [M[i] : i in I];

// the three subgroups are -- $\SO_5(3)$ and $3^4 : \SL_4(3)$ (two copies)
#M;

ChiefFactors(M[1]);
ChiefFactors(M[2]);
ChiefFactors(M[3]);

// let's now look at valid subgroups inside $\SL_4(3)$
G := SL(4,3);
M := MaximalSubgroups(G : OrderMultipleOf := 3^4);
M := [A`subgroup : A in M];

Q := [Sylow(A,3)/pCore(A,3) : A in M];

I := [i : i in [1..#Q] | #Q[i] gt 3^4 or IdentifyGroup(Q[i]) eq <3^4,7>];

M := [M[i] : i in I];

// we have two copies of $\Sp_4(3)$
#M;

ChiefFactors(M[1]);
ChiefFactors(M[2]);
