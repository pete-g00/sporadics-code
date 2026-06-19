PResidue := function(G,p)
    return NormalClosure(G, SylowSubgroup(G,p));
end;

# -----------------------------------------------------------------------------------------------------------------------------
# Using BHRD, all maximal subgroups of the following classical groups are such that no subgroup $H$ satisfies 
# $|H|_3 \geq 3^5$ and $|O_3(H)| = 1$: $\SL_4(3)$, $\SU_4(3)$ and $\Sp_4(9)$.
# -----------------------------------------------------------------------------------------------------------------------------

# -----------------------------------------------------------------------------------------------------------------------------
# $\SL_5(3)$ has no proper subgroups that are valid
# -----------------------------------------------------------------------------------------------------------------------------
G := SL(IsPermGroup, 5, 3);

M := MaximalSubgroupClassReps(G);;
M := Filtered(M, A -> Index(A, PCore(A,3)) mod 3^5 = 0);;

List(M, StructureDescription); # $\GL_4(3)$

# -----------------------------------------------------------------------------------------------------------------------------
# $\Sp_2(3) \wr \Alt(4)$ has only one proper subgroup that is valid -- $\Sp_2(3) \wr 3 \times \SL_2(3)$
# -----------------------------------------------------------------------------------------------------------------------------
G := WreathProduct(Sp(IsPermGroup, 2, 3), AlternatingGroup(4));

M := MaximalSubgroupClassReps(G);;
M := Filtered(M, A -> Index(A, PCore(A,3)) mod 3^5 = 0);;

Length(M); # should be 1
StructureDescription(M[1]) # $\SL_2(3) \wr 3 \times \SL_2(3)$

# -----------------------------------------------------------------------------------------------------------------------------
# $\Sp_2(3) \wr 3 \times \SL_2(3)$ has no proper subgroups that are valid
# -----------------------------------------------------------------------------------------------------------------------------
G := M[1];

M := MaximalSubgroupClassReps(G);;
M := Filtered(M, A -> Index(A, PCore(A,3)) mod 3^5 = 0);;

Length(M); # should be 0

# -----------------------------------------------------------------------------------------------------------------------------
# $\Sp_6(3)$ has only one subgroup that is valid -- $\SL_2(3) \times \Sp_4(3)$
# -----------------------------------------------------------------------------------------------------------------------------
G := Sp(IsPermGroup, 6, 3);

M := MaximalSubgroupClassReps(G);;
M := Filtered(M, A -> Index(A, PCore(A,3)) mod 3^5 = 0);;

Length(M); # should be 1
StructureDescription(M[1]);  # $\SL_2(3) \times \Sp_4(3)$

# -----------------------------------------------------------------------------------------------------------------------------
# $\SL_2(3) \times \Sp_4(3)$ has no proper subgroups that are valid
# -----------------------------------------------------------------------------------------------------------------------------
G := M[1];

M := MaximalSubgroupClassReps(G);;
M := Filtered(M, A -> Index(A, PCore(A,3)) mod 3^5 = 0);;

Length(M); # should be 0

# -----------------------------------------------------------------------------------------------------------------------------
# Valid subgroups of $\Sp_4(3) \times \Sp_4(3)$ -- $2^{1+4}_- \ldotp \Alt(5)$, $\Sp_4(3) \times \SL_2(3)$ (and their subgroups)
# -----------------------------------------------------------------------------------------------------------------------------
G := DirectProduct(Sp(IsPermGroup, 4, 3), Sp(IsPermGroup, 4, 3));

M := MaximalSubgroupClassReps(G);;
M := Filtered(M, A -> Index(A, PCore(A,3)) mod 3^5 = 0);;
M := List(M, A -> PResidue(A/PCore(A,3),3));;

M1 := Filtered(M, A -> PValuation(Size(A),3) = 5);;
List(M1, StructureDescription); # $2^{1+4}_- \ldotp \Alt(5)$, $\Sp_4(3) \times \SL_2(3)$

M2 := Filtered(M, A -> PValuation(Size(A),3) > 5);
List(M2, StructureDescription); # $\Sp_4(3) \times \SL_2(9)$, $\Sp_4(3) \times \SL_2(3) \times \SL_2(3)$

# -----------------------------------------------------------------------------------------------------------------------------
# Valid subgroups of $2^{1+4}_- \ldotp \Alt(5)$ - $\Sp_4(3) \times \SL_2(3)$, $\Sp_4(3) \times \SL_2(5)$, 
#                                                 $(Q_8 \times Q_8) : 3 \times \SL_2(3)$ (and their subgroups)
# -----------------------------------------------------------------------------------------------------------------------------
A := First(M1, A -> Size(A) = 99532800); # $2^{1+4}_- \ldotp \Alt(5)$

M0 := MaximalSubgroupClassReps(A);
M0 := Filtered(M0, A -> Index(A, PCore(A,3)) mod 3^5 = 0);
M0 := List(M0, A -> PResidue(A,3));
List(M0, StructureDescription); # $\Sp_4(3) \times \SL_2(3)$, $\Sp_4(3) \times \SL_2(5)$, $(Q_8 \times Q_8) : 3 \times \Sp_4(3)$

# -----------------------------------------------------------------------------------------------------------------------------
# $\Sp_4(3) \times \SL_2(5)$ has only one subgroup that is valid -- $\SL_2(3) \times \Sp_4(3)$
# -----------------------------------------------------------------------------------------------------------------------------
B := First(M0, A -> Size(A) = 6220800); # $\Sp_4(3) \times \SL_2(5)$
C := First(M0, A -> Size(A) = 9953280); # $(Q_8 \times Q_8) : 3 \times \Sp_4(3)$

M0 := MaximalSubgroupClassReps(B);;
M0 := Filtered(M0, A -> Index(A, PCore(A,3)) mod 3^5 = 0);;
M0 := List(M0, A -> PResidue(A,3));;
List(M0, StructureDescription); # $\Sp_4(3) \times \SL_2(3)$

# -----------------------------------------------------------------------------------------------------------------------------
# $(Q_8 \times Q_8) : 3 \times \Sp_4(3)$ has only one subgroup that is valid -- $\SL_2(3) \times \Sp_4(3)$
# -----------------------------------------------------------------------------------------------------------------------------
M0 := MaximalSubgroupClassReps(C);;
M0 := Filtered(M0, A -> Index(A, PCore(A,3)) mod 3^5 = 0);;
M0 := List(M0, A -> PResidue(A,3));;
List(M0, StructureDescription); # $\Sp_4(3) \times \SL_2(3)$

# -----------------------------------------------------------------------------------------------------------------------------
# Valid subgroups of $\Sp_4(3) \times \SL_2(9)$ -- $\Sp_4(3) \times \SL_2(3)$ and $\Sp_4(3) \times \SL_2(5)$
# -----------------------------------------------------------------------------------------------------------------------------
D := First(M2, A -> Size(A) = 37324800); # $\Sp_4(3) \times \SL_2(9)$

M0 := MaximalSubgroupClassReps(D);;
M0 := Filtered(M0, A -> Index(A, PCore(A,3)) mod 3^5 = 0);;
M0 := List(M0, A -> PResidue(A,3));;
List(M0, StructureDescription); # $\Sp_4(3) \times \SL_2(3)$, $\Sp_4(3) \times \SL_2(5)$

# -----------------------------------------------------------------------------------------------------------------------------
# Valid subgroups of $\Sp_4(3) \times \SL_2(3) \times \SL_2(3)$ -- $\Sp_4(3) \times \SL_2(3)$ and $(Q_8 \times Q_8) : 3 \times \SL_2(3)$
# -----------------------------------------------------------------------------------------------------------------------------
D := First(M2, A -> Size(A) = 29859840); # $\Sp_4(3) \times \SL_2(3) \times \SL_2(3)$

M0 := MaximalSubgroupClassReps(D);;
M0 := Filtered(M0, A -> Index(A, PCore(A,3)) mod 3^5 = 0);;
M0 := List(M0, A -> A/PCore(A,3));;
M0 := List(M0, A -> PResidue(A,3));;
List(M0, StructureDescription); # $\Sp_4(3) \times \SL_2(3)$, $(Q_8 \times Q_8) : 3 \times \SL_2(3)$

# -----------------------------------------------------------------------------------------------------------------------------
# Valid subgroups of $\Sp_2(3) \times \Sp_6(3)$ -- $\Sp_4(3) \times \SL_2(3)$, $(Q_8 \times Q_8) : 3 \times \SL_2(3)$
#                                                  $\SL_2(3) \wr 3 \times \SL_2(3)$ and $\SL_2(27) : 3 \times \SL_2(3)$
# -----------------------------------------------------------------------------------------------------------------------------
G := DirectProduct(Sp(IsPermGroup, 2, 3), Sp(IsPermGroup, 6, 3));

M := MaximalSubgroupClassReps(G);;
M := Filtered(M, A -> Index(A, PCore(A,3)) mod 3^5 = 0);;
M := List(M, A -> A/PCore(A,3));;
M := List(M, A -> PResidue(A,3));;

List(M, StructureDescription); # $\Sp_6(3)$, $\Sp_4(3) \times \SL_2(3)$, $\Sp_4(3) \times \SL_2(3) \times \SL_2(3)$, 
# $\SL_2(3) \wr 3 \times \SL_2(3)$, $\SL_2(27) : 3 \times \SL_2(3)$

# -----------------------------------------------------------------------------------------------------------------------------
# $\SL_2(27) : 3 \times \SL_2(3)$ has no proper subgroups that are valid
# -----------------------------------------------------------------------------------------------------------------------------
G := First(M, A -> Size(A) = 1415232); # $\SL_2(27) : 3 \times \SL_2(3)$

M := MaximalSubgroupClassReps(G);;
M := Filtered(M, A -> Index(A, PCore(A,3)) mod 3^5 = 0);;

Length(M); # should be 0

# -----------------------------------------------------------------------------------------------------------------------------
# $\Sp_2(3) \times \SL_4(3)$ has only one subgroup that is valid -- $\SL_2(3) \times \Sp_4(3)$
# -----------------------------------------------------------------------------------------------------------------------------
G := DirectProduct(Sp(IsPermGroup, 2, 3), SL(IsPermGroup, 4, 3));

M := MaximalSubgroupClassReps(G);;
M := Filtered(M, A -> Index(A, PCore(A,3)) mod 3^5 = 0);;
M := List(M, A -> A/PCore(A,3));;
M := List(M, A -> PResidue(A,3));;

List(M, StructureDescription); # $\Sp_4(3) \times \SL_2(3)$, $\SL_4(3)$ (invalid)

# -----------------------------------------------------------------------------------------------------------------------------
# Valid subgroups of $\Sp_2(3) \times \SL_3(3)$ -- $\Sp_4(3) \times \SL_2(3)$, $\Sp_4(3) \times \Alt(4)$ and $\Sp_4(3) \times 13 : 3$
# -----------------------------------------------------------------------------------------------------------------------------
G := DirectProduct(Sp(IsPermGroup, 4, 3), SL(IsPermGroup, 3, 3));

M := MaximalSubgroupClassReps(G);;
M := Filtered(M, A -> Index(A, PCore(A,3)) mod 3^5 = 0);;
M := List(M, A -> A/PCore(A,3));;
M := List(M, A -> PResidue(A,3));;

List(M, StructureDescription); # $\Sp_4(3) \times \SL_2(3)$, $\Sp_4(3) \times \Alt(4)$, $\Sp_4(3) \times 13 : 3$, 
# $\SL_3(3) x \SL_2(9)$, (invalid) $\SL_3(3) x \SL_2(3) x \SL_2(3)$ (invalid)

# -----------------------------------------------------------------------------------------------------------------------------
# $\Sp_4(3) \times 13 : 3$ has no proper subgroups that are valid
# -----------------------------------------------------------------------------------------------------------------------------
A := First(M, A -> Size(A) = 2021760); # $\Sp_4(3) \times 13 : 3$

M0 := MaximalSubgroupClassReps(A);;
M0 := Filtered(M0, A -> Index(A, PCore(A,3)) mod 3^5 = 0);;
Length(M0); # 0

# -----------------------------------------------------------------------------------------------------------------------------
# $\Sp_4(3) \times \Alt(4)$ has no proper subgroups that are valid
# -----------------------------------------------------------------------------------------------------------------------------
B := First(M, A -> Size(A) = 622080); # $\Sp_4(3) \times \Alt(4)$

M0 := MaximalSubgroupClassReps(B);;
M0 := Filtered(M0, A -> Index(B, PCore(B,3)) mod 3^5 = 0);;
Length(M0); # 0
