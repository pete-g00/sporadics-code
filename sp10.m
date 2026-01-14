M := [M1,M2,M3,M4,M5,M6,M7];
V := GModule(G);
R := [Restriction(V, Sylow(A,3)) : A in M];
I := [i : i in [1..#R]  Dimension(Fix(R[i])) eq 1];
I; // should be [ 6, 7 ]
CompositionFactors(M6);
CompositionFactors(M7);

M := [M8,M9,M10,M11,M12];
P := [LMGpCore(A,3) : A in M];
S := [LMGSylow(A,3) : A in M];
F := [PermutationRepresentation(A) : A in S];
Sf := [(F[i])(S[i]) : i in [1..#M]];
Pf := [(F[i])(P[i]) : i in [1..#M]];
G := [MinimalDegreePermutationRepresentation(A : Accept := Degree(A) - 1) : A in Sf];
Sg := [(G[i])(Sf[i]) : i in [1..#M]];
Pg := [(G[i])(Pf[i]) : i in [1..#M]];
C := [Complements(Sg[i], Pg[i]) : i in [1..#M]];
C := [[(G[i]^-1)(A) : A in C[i]] : i in [1..#M]];
C := [[(F[i]^-1)(A) : A in C[i]] : i in [1..#M]];

V := GModule(G);

R := [[Restriction(V,A) : A in T] : T in C];
[{Dimension(Fix(A)) : A in T} : T in R]; // only the third one (M10) contains 1
ChiefFactors(M10);

// TODO: Prove that the actual group satisfies all the assumptions

// Ruling out the central product
S6 := LMGSylow(M6,3);
S7 := LMGSylow(M6,3);

f7 := PermutationRepresentation(S7);
f6 := PermutationRepresentation(S6);

C6 := Subgroups(S6 : OrderEqual := 3^3);
C6 := [A`subgroup : A in C6];
C6 := [A : A in C6  IdentifyGroup(A) eq <3^3, 3>];

C7 := Subgroups(S7 : OrderEqual := 3^3);
C7 := [A`subgroup : A in C7];
C7 := [A : A in C7  IdentifyGroup(A) eq <3^3, 3>];

C6 := [A : A in C6  Normalizer(S6,A) eq S6];
C7 := [A : A in C7  Normalizer(S7,A) eq S7];
#C6; // should be 3
#C7; // should be 3

Co6 := [Complements(f6(S6), f6(A)) : A in C6];
Co7 := [Complements(f7(S7), f7(A)) : A in C7];

{{Dimension(Fix(Restriction(V,(f6^-1)(A)))) : A in X} : X in Co6}; // should be {{3}}
{{Dimension(Fix(Restriction(V,(f7^-1)(A)))) : A in X} : X in Co7}; // should be {{3, 4}}


// New work
> S := LMGSylow(M10, 3);
> P := LMGpCore(M10, 3);
>           
> f := PermutationRepresentation(S);                        
> S := f(S);
> P := f(P);
> Degree(S);
32841       
>           
> g := MinimalDegreePermutationRepresentation(S : Accept := Degree(S) - 1);                            
> S := g(S);
> P := g(P);
> Degree(S);
2187        
>           
> V := GModule(G);      
>           
> CheckDimension := function(C, d)                          
function>     C := [(g^-1)(A) : A in C];                    
function>     C := [(f^-1)(A) : A in C];                    
function>     C := [A : A in C | Dimension(Fix(Restriction(V,A))) eq d];                               
function>     C := [f(A) : A in C];                         
function>     C := [g(A) : A in C];                         
function>     return C; 
function> end function; 
>           
> C := Complements(S, P);                                   
> #C;       
7047        
>           
> C := CheckDimension(C, 1);                                
> #C;       
324         
>           
> C := [Subgroups(A : OrderEqual := 3^5) : A in C];         
> C := [[X`subgroup : X in A] : A in C];                    
> C := [X : X in A, A in C | IdentifyGroup(X) eq <3^5, 51>];
> #C;       
37908       
>           
> C := CheckDimension(C, 1);                                
> #C;       
23328       
>           
> E := [NormalSubgroups(A : OrderEqual := 3^3) : A in C];   
> E := [[X`subgroup : X in A] : A in E];                    
> E := [[X : X in A | IdentifyGroup(X) eq <3^3, 3>] : A in E];     
> #E;       
23328       
>           
> {{Dimension(Fix(Restriction(V, (f^-1)((g^-1)(A))))) : A in T} : T in E};                             
{
    { 2 },  
    { 3, 5 },           
    { 3 },  
    { 3, 4 },           
    { 4, 5 }
}           

// cohomological stuff
CohomologicalDimension(Restriction(V,M7),1);
0

