A := SO(IsPermGroup, 7, 3);
SA := SylowSubgroup(A, 3);
NilpotencyClassOfGroup(SA); # should be 5

B := DirectProduct(SL(IsPermGroup, 3, 3), SL(IsPermGroup, 4, 3));
SB := SylowSubgroup(B, 3);
NilpotencyClassOfGroup(SB); # should be 3

C := SL(IsPermGroup, 5, 3);
SC := SylowSubgroup(C, 3);
NilpotencyClassOfGroup(SC); # should be 4

D := Sp(IsPermGroup, 6, 3);
SD := SylowSubgroup(D, 3);

f := IsomorphismPcGroup(SA);
SA := Image(f);

f := IsomorphismPcGroup(SB);
SB := Image(f);

LoadPackage("ANUPQ");
IsIsomorphicPGroup(SA, SB); # should be false
