pResidue := function(G,p)
    return NormalClosure(G, Sylow(G,p));
end function;

// $A_5$ has no valid section(s)
A5 := DirectProduct(Sp(4,3), Sp(4,3));
M := MaximalSubgroups(A5);

M := [A`subgroup : A in M];
#[A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0]; // should be 0

// $\Sp_2(3) \times \SL_5(3)$ has valid section(s): $\Sp_2(3) \times \SL_4(3)$ and $\SL_5(3)$
C2 := DirectProduct(Sp(2,3), SL(5,3));
M := MaximalSubgroups(C2);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 4
ChiefFactors(M[1]);
ChiefFactors(M[2]);
ChiefFactors(M[3]);
ChiefFactors(M[4]);

// $\SL_4(3) \times \SL_2(3) \times \SL_2(3)$ has valid section(s): $\SL_4(3) \times \SL_2(3)$ and $\SL_4(3) \times (Q_8 \times Q_8) : 3$
C3 := DirectProduct(DirectProduct(SL(4,3), SL(2,3)), SL(2,3));
M := MaximalSubgroups(C3);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 6
ChiefFactors(M[1]);
ChiefFactors(M[2]);
ChiefFactors(M[3]);
ChiefFactors(M[4]);
ChiefFactors(M[5]);
ChiefFactors(M[6]);

// $\SL_4(3) \times \SL_2(9)$ has valid section(s): $\SL_4(3) \times \SL_2(3)$, $\SL_4(3) \times \SL_2(5)$
A := SL(2,9);
A := WriteOverSmallerField(A, GF(3));
C4 := DirectProduct(SL(4,3), A);
M := MaximalSubgroups(C4);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 4
ChiefFactors(M[1]);
ChiefFactors(M[2]);
ChiefFactors(M[3]);
ChiefFactors(M[4]);

// $\SL_4(3) \times \Sp_4(3)$ has valid section(s): $\SL_4(3) \times \SL_2(3)$, $\SL_3(3) \times \Sp_4(3)$, $\SL_4(3) \times \SL_2(9)$,
// $\Sp_4(3) \times \Sp_4(3)$, $\SL_4(3) \times \SL_2(3) \times \SL_2(3)$, $\SL_4(3) \times 2^{1+4}_- \ldotp \Alt(5)$
C5 := DirectProduct(SL(4,3), Sp(4,3));
M := MaximalSubgroups(C5);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 9
ChiefFactors(M[1]);
ChiefFactors(M[2]);
ChiefFactors(M[3]);
ChiefFactors(M[4]);
ChiefFactors(M[5]);
ChiefFactors(M[6]);
ChiefFactors(M[7]);
ChiefFactors(M[8]);
ChiefFactors(M[9]);

// $\SL_2(3) \times \Sp_6(3)$ has valid section(s): $\Sp_6(3)$
C6 := DirectProduct(SL(2,3), Sp(6,3));
M := MaximalSubgroups(C6);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 2
ChiefFactors(M[1]);
ChiefFactors(M[2]);

// $13 : 3 \times \Sp_6(3)$ has valid section(s): $\Sp_6(3)$
A := MaximalSubgroups(SL(3,3) : OrderEqual := 13 * 3);
A := A[1]`subgroup;
C7 := DirectProduct(A, Sp(6,3));
M := MaximalSubgroups(C7);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 2
ChiefFactors(M[1]);
ChiefFactors(M[2]);

// $\SL_2(3) \times \SL_3(3) \times \Sp_4(3)$ has valid section(s) : $\SL_3(3) \times \Sp_4(3)$
C8 := DirectProduct(DirectProduct(SL(2,3), SL(3,3)), Sp(4,3));
M := MaximalSubgroups(C8);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 2
ChiefFactors(M[1]);
ChiefFactors(M[2]);

// $\SL_3(3) \times \Sp_6(3)$ has valid section(s): $\SL_3(3) \times \SL_2(3^3)$, $\SL_3(3) \times \SL_2(3) \wr 3$, $\SL_3(3) \times \Sp_4(3)$,
// $13 : 3 \times \Sp_6(3)$, $\Sp_4(3) \times \SL_2(3) \times \SL_2(3)$, $\Sp_6(3) \times \SL_2(3)$
C9 := DirectProduct(SL(3,3), Sp(6,3));
M := MaximalSubgroups(C9);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 8
ChiefFactors(M[1]);
ChiefFactors(M[2]);
ChiefFactors(M[3]);
ChiefFactors(M[4]);
ChiefFactors(M[5]);
ChiefFactors(M[6]);
ChiefFactors(M[7]);
ChiefFactors(M[8]);

// $\SL_2(3) \times \Sp_4(3) \times \Sp_4(3)$ has valid section(s): $\Sp_4(3) \times \Sp_4(3)$, $\SL_2(3) \times \Sp_4(3) \times \SL_2(9)$
C11 := DirectProduct(DirectProduct(SL(2,3), Sp(4,3)), Sp(4,3));
M := MaximalSubgroups(C11);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 6
ChiefFactors(M[1]);
ChiefFactors(M[2]);
ChiefFactors(M[3]);
ChiefFactors(M[4]);
ChiefFactors(M[5]);
ChiefFactors(M[6]);

// $\Sp_6(3) \times (Q_8 \times Q_8) : 3$ has valid section(s): $\Sp_6(3)$ and $\Sp_6(3) \times \SL_2(3)$
A := DirectProduct(SL(2,3), SL(2,3));
A := MaximalSubgroups(A);
A := [X`subgroup : X in A];
A := [X : X in A | X eq pResidue(X,3) and #X eq 8 * 8 * 3];
A := A[1];
C12 := DirectProduct(Sp(6,3), A);
M := MaximalSubgroups(C12);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 6
ChiefFactors(M[1]);
ChiefFactors(M[2]);
ChiefFactors(M[3]);
ChiefFactors(M[4]);
ChiefFactors(M[5]);
ChiefFactors(M[6]);

// $\SL_2(3) \times \SL_2(3) \times \Sp_6(3)$ has valid section(s): $\SL_2(3)^3 \times \Sp_4(3)$, $\SL_2(3) \times \Sp_6(3)$
// and $(Q_8 \times Q_8) : 3 \times \Sp_6(3)$
C13 := DirectProduct(DirectProduct(SL(2,3), SL(2,3)), Sp(6,3));
M := MaximalSubgroups(C13);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 7
ChiefFactors(M[1]);
ChiefFactors(M[2]);
ChiefFactors(M[3]);
ChiefFactors(M[4]);
ChiefFactors(M[5]);
ChiefFactors(M[6]);
ChiefFactors(M[7]);

// $\Sp_4(3^2) \times \SL_2(3)$ has valid section(s): $\Sp_4(3^2)$
A := Sp(4, 3^2);
A := WriteOverSmallerField(A, GF(3));
C14 := DirectProduct(A, SL(2,3));
M := MaximalSubgroups(C14);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 2
ChiefFactors(M[1]);
ChiefFactors(M[2]);

// $\SL_2(3) \times \Sp_8(3)$ has valid section(s): $\SL_4(3) \times \SL_2(3)$, $\SU_4(3) \times \SL_2(3)$, $\Sp_4(9) \times \SL_2(3)$,
// $\SL_2(3) \times \Sp_4(3) \times \Sp_4(3)$, $\SL_2(3) \times \SL_2(3) \times \Sp_6(3)$, $\SL_2(3) \times \Sp_6(3)$, $\Sp_8(3)$
C15 := DirectProduct(SL(2,3), Sp(8,3));
M := MaximalSubgroups(C15);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 9
ChiefFactors(M[1]);
ChiefFactors(M[2]);
ChiefFactors(M[3]);
ChiefFactors(M[4]);
ChiefFactors(M[5]);
ChiefFactors(M[6]);
ChiefFactors(M[7]);
ChiefFactors(M[8]);
ChiefFactors(M[9]);

// $\SL_2(5) \times \Sp_6(3)$ has valid section(s): $\Sp_6(3) \times \SL_2(3)$ and $\Sp_6(3)$
A := SL(2,9);
A := MaximalSubgroups(A : OrderEqual := 120);
A := [X`subgroup : X in M];
A := M[1];
C16 := DirectProduct(A, Sp(6,3));
M := MaximalSubgroups(C16);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 3
ChiefFactors(M[1]);
ChiefFactors(M[2]);
ChiefFactors(M[3]);

// $2^{1+4}_- \ldotp \Alt(5) \times \Sp_6(3)$ has valid section(s): $\Sp_6(3)$, $\SL_2(3) \times \Sp_6(3)$, 
// $(Q_8 \times Q_8) : 3 \times \Sp_6(3)$ and $\SL_2(5) \times \Sp_6(3)$
A := Sp(4,3);
A := MaximalSubgroups(A : OrderEqual := 2^5 * 60);
A := A[1]`subgroup;
C17 := DirectProduct(A, Sp(6,3));
M := MaximalSubgroups(C17);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 4
ChiefFactors(M[1]);
ChiefFactors(M[2]);
ChiefFactors(M[3]);
ChiefFactors(M[4]);

// $\SL_2(9) \times \Sp_6(3)$ has valid section(s): $\SL_2(3) \times \Sp_4(3) \times \SL_2(9)$, $\Sp_6(3) \times \SL_2(3)$,
// $\Sp_6(3)$ and $\Sp_6(3) \times \SL_2(5)$
A := SL(2,9);
A := WriteOverSmallerField(A, GF(3));
C18 := DirectProduct(A, Sp(6,3));
M := MaximalSubgroups(C18);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 6
ChiefFactors(M[1]);
ChiefFactors(M[2]);
ChiefFactors(M[3]);
ChiefFactors(M[4]);
ChiefFactors(M[5]);
ChiefFactors(M[6]);

// $\Sp_4(3) \times \SL_2(3^3) : 3$ has valid section(s): $\Sp_4(3) \times \SL_2(3^3)$
A := Sp(6,3);
A := MaximalSubgroups(A : OrderEqual := #SL(2,3^3) * 3);
A := A[1]`subgroup;
C19 := DirectProduct(Sp(4,3), A);
M := MaximalSubgroups(C19);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 1
ChiefFactors(M[1]);

// $\Sp_4(3) \times \SL_2(3) \wr 3$ has valid section(s): $\Sp_4(3) \times \SL_2(3)^3$
A := Sp(6,3);
A := MaximalSubgroups(A : OrderEqual := #SL(2,3)^3 * 6);
A := pResidue(A[1]`subgroup,3);
C20 := DirectProduct(Sp(4,3), A);
M := MaximalSubgroups(C20);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 4
ChiefFactors(M[1]);
ChiefFactors(M[2]);
ChiefFactors(M[3]);
ChiefFactors(M[4]);

// $\Sp_4(3) \times \Sp_6(3)$ has valid section(s): $\Sp_4(3) \times \SL_2(3^3) : 3$, $\Sp_4(3) \times \SL_3(3)$, $\Sp_4(3) \times \SU_3(3)$,
// $\Sp_4(3) \times \SL_2(3) \wr 3$, $\SL_3(3) \times \Sp_4(3)$, $\Sp_4(3) \times \Sp_4(3) \times \SL_2(3)$, $\Sp_4(3) \times \Sp_4(3)$,
// $\Sp_6(3) \times \SL_2(3)$, $\Sp_6(3) \times \SL_2(9)$, $\Sp_6(3) \times \SL_2(3)^2$, $\Sp_6(3) \times 2^{1+4}_- \ldotp \Alt(5)$
C21 := DirectProduct(Sp(4,3), Sp(6,3));
M := MaximalSubgroups(C21);
M := [A`subgroup : A in M];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^7 eq 0];
#M; // should be 12
ChiefFactors(M[1]);
ChiefFactors(M[2]);
ChiefFactors(M[3]);
ChiefFactors(M[4]);
ChiefFactors(M[5]);
ChiefFactors(M[6]);
ChiefFactors(M[7]);
ChiefFactors(M[8]);
ChiefFactors(M[9]);
ChiefFactors(M[10]);
ChiefFactors(M[11]);
ChiefFactors(M[12]);
