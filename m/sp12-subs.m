LMGpResidue := function(G, p)
    return LMGNormalClosure(G, LMGSylow(G, p));
end function;

M := ClassicalMaximals("S", 12, 3);
V := [GModule(A) : A in M];
I := [i : i in [1..#M] | Dimension(Fix(Restriction(V[i], LMGSylow(M[i],3)))) eq 1];
I; // [1, 2, 3, 4, 5, 6, 10, 14, 16, 17, 18]

M0 := LMGMaximalSubgroups(LMGpResidue(M[10], 3));
M0 := [A`subgroup : A in M0];
M0 := [A : A in M0 | LMGIndex(A, LMGpCore(A,3)) mod 3^7 eq 0];
#[A : A in M0 | Dimension(Fix(Restriction(V[10], LMGSylow(A,3)))) eq 1]; // should be 0

M0 := LMGMaximalSubgroups(M[14]);
M0 := [A`subgroup : A in M0];
M0 := [A : A in M0 | LMGIndex(A, LMGpCore(A,3)) mod 3^7 eq 0];
#[A : A in M0 | Dimension(Fix(Restriction(V[14], LMGSylow(A,3)))) eq 1]; // should be 0
