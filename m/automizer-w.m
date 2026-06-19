/*
www-ATLAS of Group Representations.
2.Suz represented as 12 x 12 matrices over GF(3).
*/

F:=GF(3);

x:=CambridgeMatrix(1,F,12,[
"121200112020",
"112111102110",
"020201122010",
"001110010002",
"222020100112",
"210012002101",
"220221021122",
"012011112200",
"021220012212",
"102221210120",
"012222210001",
"222112011021"]);

y:=CambridgeMatrix(1,F,12,[
"001000000000",
"112000000000",
"202000000000",
"000010000000",
"121220000000",
"000000100000",
"000000001000",
"000000000100",
"000001000000",
"000001121200",
"011212110210",
"011210201001"]);

G<x,y>:=MatrixGroup<12,F|x,y>;

S := LMGSylow(G, 3);
M := Subgroups(S : OrderMultipleOf := 3^5, OrderDividing := 3^6);
M := [A`subgroup : A in M];

NGM := [LMGNormalizer(G,A) : A in M];
I := [i : i in [1..#M] | LMGpCore(NGM[i],3) eq M[i]];

#I; // should be 2 (i.e. both $P$ and $Q$ are essential in $N_F(W)$)

C := Subgroups(S : OrderEqual := 3^2);
C := [A`subgroup : A in C];
C := [A : A in C | IsElementaryAbelian(A)];

NGC := [LMGNormalizer(G,A) : A in C];
I := [i : i in [1..#C] | LMGpCore(NGC[i],3) eq C[i]];

#I; // should be 2 ($\calF$-conjugates of $X$, but not $S$-conjugate)
IsConjugate(G, C[I[1]], C[I[2]]); // should be true

NGS := LMGNormalizer(G, S);
Index(NGS, S); // should be 32
