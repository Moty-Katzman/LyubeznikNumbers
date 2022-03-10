
+ M2 --no-readline --print-width 200
Macaulay2, version 1.19.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, InverseSystems, LLLBases, MinimalPrimes, PrimaryDecomposition, ReesAlgebra, Saturation, TangentCone

i1 : R0=ZZ/2[s,t,w,x,y,z, MonomialOrder=>Product(2,4)]

stdio:1:6:(3): error: unrecognized ordering item 2*4

i2 :      R0=ZZ/2[s,t,w,x,y,z, MonomialOrder=>ProductOrder(2,4)]


o2 = R0

o2 : PolynomialRing

i3 :      R0=ZZ/2[s,t,w,x,y,z, MonomialOrder=>ProductOrder(2,4)]
I0=ideal(w-s^4, x-s^3*t, y-s*t^3, z-t^4);
G=gens gb I0;
I=selectInSubring(1,G)


o3 = R0

o3 : PolynomialRing

i4 : 
o4 : Ideal of R0

i5 : 
              1        14
o5 : Matrix R0  <--- R0

i6 : 
o6 = | xy+wz y3+xz2 wy2+x2z x3+w2y |

              1        4
o6 : Matrix R0  <--- R0

i7 :      I

o7 = | xy+wz y3+xz2 wy2+x2z x3+w2y |

              1        4
o7 : Matrix R0  <--- R0

i8 : I=selectInSubring(1,G)


o8 = 0

              1
o8 : Matrix R0  <--- 0
G
i9 :      G

o9 = | xy+wz y3+xz2 wy2+x2z x3+w2y sz+ty sx+tw sy2+txz swy+tx2 s2y+t2x t4+z st3+y s2t2w+x2 s3t+x s4+w |

              1        14
o9 : Matrix R0  <--- R0

i10 : I=selectInSubring(1,G)

o10 = | xy+wz y3+xz2 wy2+x2z x3+w2y |

               1        4
o10 : Matrix R0  <--- R0

i11 : R0=ZZ/2[s,t,w,x,y,z, MonomialOrder=>ProductOrder(2,4)]
I0=ideal(w-s^4, x-s^3*t, y-s*t^3, z-t^4);
G=gens gb I0;
I=selectInSubring(1,G)


o11 = R0

o11 : PolynomialRing

i12 : 
o12 : Ideal of R0

i13 : 
               1        14
o13 : Matrix R0  <--- R0

i14 : 
o14 = | xy+wz y3+xz2 wy2+x2z x3+w2y |

               1        4
o14 : Matrix R0  <--- R0

i15 :       mingens ideal I

o15 = | xy+wz y3+xz2 wy2+x2z x3+w2y |

               1        4
o15 : Matrix R0  <--- R0

i16 : restart;


--loadPackage "TestIdeals"
--loadPackage "BinomialEdgeIdeals"


---load "~/Dropbox/Macaulay2/My Libraries/my PosChar July 2019.m2"
---load "~/Dropbox/Macaulay2/My Libraries/randomObjects.m2"




--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------
--                      F U N C T I O N S 
--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------

--The following raises an ideal/matrix to a Frobenius power;
frobeniusPowerX=method()

frobeniusPowerX(Ideal,ZZ) := (I1,e1) ->(
     R1:=ring I1;
     p1:=char R1;
     local answer;
     G1:=first entries gens I1;
     if (#G1==0) then answer=ideal(0_R1) else answer=ideal(apply(G1, j->j^(p1^e1)));
     answer
);



frobeniusPowerX(Matrix,ZZ) := (M,e) ->(
R:=ring M;
p:=char R;
G:=entries M;
local i;
local j;
L:={};
apply(G, i->
{
	L=append(L,apply(i, j->j^(p^e)));
});
matrix L
);


--- Given matrices A, B with target R^alpha find all v\in R^alpha such that B v \in Image A
--- by computing a kernel
matrixColon= (A, B) ->(
---t0:=cpuTime();
assert(target(A)==target(B));
m:=rank source B;
w:=map(coker A, source B, B);
answer:=gens kernel w;
---print(cpuTime()-t0);
answer
)


--- Given a generating morphism U:coker(A) -> F(coker A), compute a generating root U:coker(L) -> F(coker L)
generatingRoot= (A,U) ->(
	R:=ring(A);
	L:=A;
	alpha:=rank target A;
	LL:=transpose matrix{toList(alpha:0_R)};
	while ((( L)%( LL))!=0) do
	{
		LL=L;
		L=L | matrixColon(frobeniusPowerX(L,1),U);
		L=mingens image L;
---		print("=================================================================");
---		print(L);
	};
	L
)



---compute a generating morphism for H^(dim R -i)_I(R)
---the output is (A,U) where U:coker(A) -> F(coker A) is the generating morphism
generatingMorphism= (I,i) ->(
	R:=ring(I); p:=char(R);
	Ip:=gens frobeniusPowerX(ideal I,1);
	M:=coker I;
	Mp:=coker Ip;
---	resM:=res M;
---	resMp:=res Mp;
	f:=inducedMap(M,Mp);
	resf:=res f;
	E:=Ext^i(f, R^1);
	(source E, E)
)


MfilterSequence =(A,l)->
(
    local f; local  answer; local   counter; local r ;
    R := ring I;
    V:=ideal(vars(R));
    T:=target(A);
--    answer=findMaximalRegularSequence(gens I);
    answer={};
    while ((#answer)<l) do
    {
--       print(#answer);
       J:=ideal(append(answer,0_R));
       B:=J*T+image(A);
       f=false;
       counter=0;
       while (not f) do
       {
--	   print(counter);
	   if (counter<dim(R)) then
	       r=V_counter
	   else
               r=randomElementInIdeal(((counter-dim(R))//20),V);
	   c1:=gens (B:r);
--	   print("c1",c1);
	   c2:=prune subquotient(c1, gens B);
--	   print("c2",c2);
	   c3:=radical annihilator c2;
--	   print("c3",c3);
	   c4:=(gens(V))%(gens(c3));
--	   print("c4",c4);
	   f=(c4==0);
	   counter=counter+1;
       };
       answer=append(answer, r);
---       print("MfilterSequence",l,dim(R),counter,answer);
    };
    answer
)


randomElementInIdeal=(d,I)->
(
    local answer;
    R := ring I;
    g:=gens I;
    n:=rank source gens I;
    m:=random(R^{n:d},R^1);
--    print(m,g);
    answer=entries (g*m);
    answer=first first answer;
--    print (answer);
    answer
)

   

saturation=(J,f,N)->
(
J:f^N
)

limClosure =(G,n)->
(
    if ((#G)<n) then 
    {
	print (" *** FATAL ERROR *** LimClosure, sequence too short");
	return;
    };
    R :=ring (G#0);
    p:=char(R);
    genI:= apply(0..(n-1), i->G#i);
    J:=ideal(genI);
    P:=toList genI;
    PP:=product(P);
    lastJ:=ideal(genI);
    f:=true;
    while (f) do
    {
---print(mingens J);	
    	J=frobeniusPowerX(J,1);
--	apply(P, z-> {J=J:z});
--    	J=J:PP;
    	J=saturation(J,PP,p-1); J=substitute(J,R);
	f= (gens(J)%gens(lastJ))!=0;
	if (f) then
	{
	    lastJ=J;
        };
---    	print(f,J);
    };  
    J
)
---limClosure((x_{1,1},x_{1,2},x_{1,3}),2)
---time limClosure(G,h)


lowLimClosure =(G,n)->
(
    R :=ring (G#0); 
    if ((#G)<n) then 
    {
	print (" *** FATAL ERROR *** lowLimClosure, sequence too short");
	return;
    }
    else if (n==1) then 
    {
	return ideal(0_R);
    };
    LC:=limClosure(G,n-1);
    g:=G#(n-1);
    saturate(LC,g)
)

---------------------------------------------------------------------------------------------------
---load "~/Dropbox/Rodney/LClibNew.m2"

--- Given a generating morphism U:A/B -> F(A/B), compute a generating root U:coker(L) -> F(coker L)
--- A, B, U matrices with same target
generatingSubquotientRoot= (A,B,U) ->(
	R:=ring(A);
	B0:=B;
	Ap:=frobeniusPowerX(A,1);
	Bp:=frobeniusPowerX(B0,1);
	assert ((U*A)%(Ap)==0);
	assert ((U*B0)%(Bp)==0);
	B1:= matrixColon(Bp, U);
	B1=matrix entries B1;
	B1= gens (intersect(image(B1), image(A)));
	while ((B1%B0)!=0) do
	{
	    B0=B1;
	    Bp=frobeniusPowerX(B0,1);
	    B1= matrixColon(Bp, U);
	    B1=matrix entries B1;
	    B1= gens (intersect(image(B1), image(A)));
	};
    (A,B1,prune subquotient(A,B1))
)



Lyubeznik = (A,U,i) ->(
local t; local answer; local F; local  L0; local  L1; 
local f; local  g; local  h; local  B; local  V; local  C;
local X; local Y;
local W;
R:=ring (A);
p:=char(R);
T:=target(A);
if (i>0) then
{
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    Q:=prune subquotient(gens B, gens C);
    if (Q==0) then
    {
	answer=0;
    }
    else
    {
	(X,Y,W)=generatingSubquotientRoot (gens B, gens C,V);
	if (W==0) then
	{
	    answer=0;
	}
    	else
    	{
    	    G1:=Hom(coker vars(R), W); 
--    	    answer=length(G1);   --- fails if G1 is not graded
    	    answer=rank source mingens G1;   
	};
    };
};
------------------------------------
if (i==0) then
{
    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
	if (X==0) then
	{
	    answer=0;
	}
    	else
    	{
     	    G1:=Hom(coker vars(R),  W); 
--    	    answer=length(G1);  --- fails if G1 is not graded
    	    answer=rank source mingens G1;   
	};
};
answer
)

LyubeznikTable  = (I) ->
(
    local i;  local  j;
    answer := new MutableHashTable;
    d:=dim coker I;
    R := ring I;
    n:= dim R;
    for j from 0 to d do
    {
	E:=generatingMorphism(I,n-j);
	if (not ((E#1)==0)) then
	{
	    U:=matrix entries (E#1);
	    A:=relations E#0; A=matrix entries A;
	    G:=generatingRoot(A,U);
    	    for i from 0 to j do
    	    {
	     	Z:=Lyubeznik (G,U,i);
	     	if (Z>0) then answer#(i,j)=Z;
---		print("***",i,j,Z);
    	    };
	};
    };
answer
)


R=ZZ/2[A_1, A_2,B_1,B_2,C_1,C_2];
I=gens ideal(A_1*A_2,  B_1*B_2,  C_1*C_2,  A_1*B_1*C_1,   A_2*B_2*C_2 );
time LT=LyubeznikTable(I)
peek(LT)

 
R=ZZ/2[A1,A2,A3,A4, B1,B2,B3,B4];
I=gens ideal(A1*A2*A3*A4, B1*B2*B3*B4, A1*A3*A4*B1*B2*B3, A2*A3*A4*B1*B4,  
    A1*A2*A4*B2*B4,   A1*A2*A3*B3*B4,  A2*A4*B1*B2*B4, A2*A3*B1*B3*B4, A1*A2*B2*B3*B4)
time LT=LyubeznikTable(I)
peek(LT)
 


--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------
--                       C A L C U L A T I O N S    A N D    E X A M P L E S
--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------

Macaulay2, version 1.19.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, InverseSystems, LLLBases, MinimalPrimes, PrimaryDecomposition, ReesAlgebra, Saturation, TangentCone

i1 :                                                                                                
o1 = frobeniusPowerX

o1 : MethodFunction

i2 :                                         
i3 :                                                                            
i4 :                                                             
o4 = matrixColon

o4 : FunctionClosure

i5 :                                                                                      
o5 = generatingRoot

o5 : FunctionClosure

i6 :                                                                                 
o6 = generatingMorphism

o6 : FunctionClosure

i7 :                                                                                                                                                                                                    
o7 = MfilterSequence

o7 : FunctionClosure

i8 :                                                                       
o8 = randomElementInIdeal

o8 : FunctionClosure

i9 :                               
o9 = saturation

o9 : FunctionClosure

i10 :                                                                                                                                                                                           
o10 = limClosure

o10 : FunctionClosure

i11 :                                                                                                                   
o11 = lowLimClosure

o11 : FunctionClosure

i12 :                                                                                                                                                       
o12 = generatingSubquotientRoot

o12 : FunctionClosure

i13 :                                                                                                                                                                                                                                                                                                                                                                                                                   stdio:295:13:(3): warning: local declaration of G1 shields variable with same name

o13 = Lyubeznik

o13 : FunctionClosure

i14 :                                                                                                                                                       
o14 = LyubeznikTable

o14 : FunctionClosure

i15 :             
i16 : 
              1       5
o16 : Matrix R  <--- R

i17 :      -- used 2.82279 seconds

o17 = MutableHashTable{...3...}

o17 : MutableHashTable

i18 : 
o18 = MutableHashTable{(0, 2) => 1}
                       (2, 3) => 1
                       (3, 3) => 1

i19 :             
i20 :       
o20 = | A1A2A3A4 B1B2B3B4 A1A3A4B1B2B3 A2A3A4B1B4 A1A2A4B2B4 A1A2A3B3B4 A2A4B1B2B4 A2A3B1B3B4 A1A2B2B3B4 |

              1       9
o20 : Matrix R  <--- R

i21 : R=ZZ/2[t,x,y,z]
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);

R=ZZ/2[t,x,y,z]
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
  C-c C-cstdio:142:8:(3):[4]: error: interrupted
     -- used 57.6919 seconds

i22 : R=ZZ/2[t,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;


i23 : stdio:341:14:(3): error: no method for binary operator * applied to objects:
--            w (of class Symbol)
--      *     z (of class R)

i24 : stdio:342:3:(3): error: no method found for applying generators to:
     argument   :  | A1A2A3A4 B1B2B3B4 A1A3A4B1B2B3 A2A3A4B1. (of class Matrix)

i25 :       restart;


--loadPackage "TestIdeals"
--loadPackage "BinomialEdgeIdeals"


---load "~/Dropbox/Macaulay2/My Libraries/my PosChar July 2019.m2"
---load "~/Dropbox/Macaulay2/My Libraries/randomObjects.m2"




--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------
--                      F U N C T I O N S 
--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------

--The following raises an ideal/matrix to a Frobenius power;
frobeniusPowerX=method()

frobeniusPowerX(Ideal,ZZ) := (I1,e1) ->(
     R1:=ring I1;
     p1:=char R1;
     local answer;
     G1:=first entries gens I1;
     if (#G1==0) then answer=ideal(0_R1) else answer=ideal(apply(G1, j->j^(p1^e1)));
     answer
);



frobeniusPowerX(Matrix,ZZ) := (M,e) ->(
R:=ring M;
p:=char R;
G:=entries M;
local i;
local j;
L:={};
apply(G, i->
{
	L=append(L,apply(i, j->j^(p^e)));
});
matrix L
);


--- Given matrices A, B with target R^alpha find all v\in R^alpha such that B v \in Image A
--- by computing a kernel
matrixColon= (A, B) ->(
---t0:=cpuTime();
assert(target(A)==target(B));
m:=rank source B;
w:=map(coker A, source B, B);
answer:=gens kernel w;
---print(cpuTime()-t0);
answer
)


--- Given a generating morphism U:coker(A) -> F(coker A), compute a generating root U:coker(L) -> F(coker L)
generatingRoot= (A,U) ->(
	R:=ring(A);
	L:=A;
	alpha:=rank target A;
	LL:=transpose matrix{toList(alpha:0_R)};
	while ((( L)%( LL))!=0) do
	{
		LL=L;
		L=L | matrixColon(frobeniusPowerX(L,1),U);
		L=mingens image L;
---		print("=================================================================");
---		print(L);
	};
	L
)



---compute a generating morphism for H^(dim R -i)_I(R)
---the output is (A,U) where U:coker(A) -> F(coker A) is the generating morphism
generatingMorphism= (I,i) ->(
	R:=ring(I); p:=char(R);
	Ip:=gens frobeniusPowerX(ideal I,1);
	M:=coker I;
	Mp:=coker Ip;
---	resM:=res M;
---	resMp:=res Mp;
	f:=inducedMap(M,Mp);
	resf:=res f;
	E:=Ext^i(f, R^1);
	(source E, E)
)


MfilterSequence =(A,l)->
(
    local f; local  answer; local   counter; local r ;
    R := ring I;
    V:=ideal(vars(R));
    T:=target(A);
--    answer=findMaximalRegularSequence(gens I);
    answer={};
    while ((#answer)<l) do
    {
--       print(#answer);
       J:=ideal(append(answer,0_R));
       B:=J*T+image(A);
       f=false;
       counter=0;
       while (not f) do
       {
--	   print(counter);
	   if (counter<dim(R)) then
	       r=V_counter
	   else
               r=randomElementInIdeal(((counter-dim(R))//20),V);
	   c1:=gens (B:r);
--	   print("c1",c1);
	   c2:=prune subquotient(c1, gens B);
--	   print("c2",c2);
	   c3:=radical annihilator c2;
--	   print("c3",c3);
	   c4:=(gens(V))%(gens(c3));
--	   print("c4",c4);
	   f=(c4==0);
	   counter=counter+1;
       };
       answer=append(answer, r);
---       print("MfilterSequence",l,dim(R),counter,answer);
    };
    answer
)


randomElementInIdeal=(d,I)->
(
    local answer;
    R := ring I;
    g:=gens I;
    n:=rank source gens I;
    m:=random(R^{n:d},R^1);
--    print(m,g);
    answer=entries (g*m);
    answer=first first answer;
--    print (answer);
    answer
)

   

saturation=(J,f,N)->
(
J:f^N
)

limClosure =(G,n)->
(
    if ((#G)<n) then 
    {
	print (" *** FATAL ERROR *** LimClosure, sequence too short");
	return;
    };
    R :=ring (G#0);
    p:=char(R);
    genI:= apply(0..(n-1), i->G#i);
    J:=ideal(genI);
    P:=toList genI;
    PP:=product(P);
    lastJ:=ideal(genI);
    f:=true;
    while (f) do
    {
---print(mingens J);	
    	J=frobeniusPowerX(J,1);
--	apply(P, z-> {J=J:z});
--    	J=J:PP;
    	J=saturation(J,PP,p-1); J=substitute(J,R);
	f= (gens(J)%gens(lastJ))!=0;
	if (f) then
	{
	    lastJ=J;
        };
---    	print(f,J);
    };  
    J
)
---limClosure((x_{1,1},x_{1,2},x_{1,3}),2)
---time limClosure(G,h)


lowLimClosure =(G,n)->
(
    R :=ring (G#0); 
    if ((#G)<n) then 
    {
	print (" *** FATAL ERROR *** lowLimClosure, sequence too short");
	return;
    }
    else if (n==1) then 
    {
	return ideal(0_R);
    };
    LC:=limClosure(G,n-1);
    g:=G#(n-1);
    saturate(LC,g)
)

---------------------------------------------------------------------------------------------------
---load "~/Dropbox/Rodney/LClibNew.m2"

--- Given a generating morphism U:A/B -> F(A/B), compute a generating root U:coker(L) -> F(coker L)
--- A, B, U matrices with same target
generatingSubquotientRoot= (A,B,U) ->(
	R:=ring(A);
	B0:=B;
	Ap:=frobeniusPowerX(A,1);
	Bp:=frobeniusPowerX(B0,1);
	assert ((U*A)%(Ap)==0);
	assert ((U*B0)%(Bp)==0);
	B1:= matrixColon(Bp, U);
	B1=matrix entries B1;
	B1= gens (intersect(image(B1), image(A)));
	while ((B1%B0)!=0) do
	{
	    B0=B1;
	    Bp=frobeniusPowerX(B0,1);
	    B1= matrixColon(Bp, U);
	    B1=matrix entries B1;
	    B1= gens (intersect(image(B1), image(A)));
	};
    (A,B1,prune subquotient(A,B1))
)



Lyubeznik = (A,U,i) ->(
local t; local answer; local F; local  L0; local  L1; 
local f; local  g; local  h; local  B; local  V; local  C;
local X; local Y;
local W;
R:=ring (A);
p:=char(R);
T:=target(A);
if (i>0) then
{
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    Q:=prune subquotient(gens B, gens C);
    if (Q==0) then
    {
	answer=0;
    }
    else
    {
	(X,Y,W)=generatingSubquotientRoot (gens B, gens C,V);
	if (W==0) then
	{
	    answer=0;
	}
    	else
    	{
    	    G1:=Hom(coker vars(R), W); 
--    	    answer=length(G1);   --- fails if G1 is not graded
    	    answer=rank source mingens G1;   
	};
    };
};
------------------------------------
if (i==0) then
{
    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
	if (X==0) then
	{
	    answer=0;
	}
    	else
    	{
     	    G1:=Hom(coker vars(R),  W); 
--    	    answer=length(G1);  --- fails if G1 is not graded
    	    answer=rank source mingens G1;   
	};
};
answer
)

LyubeznikTable  = (I) ->
(
    local i;  local  j;
    answer := new MutableHashTable;
    d:=dim coker I;
    R := ring I;
    n:= dim R;
    for j from 0 to d do
    {
	E:=generatingMorphism(I,n-j);
	if (not ((E#1)==0)) then
	{
	    U:=matrix entries (E#1);
	    A:=relations E#0; A=matrix entries A;
	    G:=generatingRoot(A,U);
    	    for i from 0 to j do
    	    {
	     	Z:=Lyubeznik (G,U,i);
	     	if (Z>0) then answer#(i,j)=Z;
---		print("***",i,j,Z);
    	    };
	};
    };
answer
)


Macaulay2, version 1.19.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, InverseSystems, LLLBases, MinimalPrimes, PrimaryDecomposition, ReesAlgebra, Saturation, TangentCone

i1 :                                                                                                
o1 = frobeniusPowerX

o1 : MethodFunction

i2 :                                         
i3 :                                                                            
i4 :                                                             
o4 = matrixColon

o4 : FunctionClosure

i5 :                                                                                      
o5 = generatingRoot

o5 : FunctionClosure

i6 :                                                                                 
o6 = generatingMorphism

o6 : FunctionClosure

i7 :                                                                                                                                                                                                    
o7 = MfilterSequence

o7 : FunctionClosure

i8 :                                                                       
o8 = randomElementInIdeal

o8 : FunctionClosure

i9 :                               
o9 = saturation

o9 : FunctionClosure

i10 :                                                                                                                                                                                           
o10 = limClosure

o10 : FunctionClosure

i11 :                                                                                                                   
o11 = lowLimClosure

o11 : FunctionClosure

i12 :                                                                                                                                                       
o12 = generatingSubquotientRoot

o12 : FunctionClosure

i13 :                                                                                                                                                                                                                                                                                                                                                                                                                   stdio:295:13:(3): warning: local declaration of G1 shields variable with same name

o13 = Lyubeznik

o13 : FunctionClosure

i14 :                                                                                                                                                       
o14 = LyubeznikTable

o14 : FunctionClosure

i15 :             R=ZZ/2[t,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;


i16 : stdio:331:14:(3): error: no method for binary operator * applied to objects:
--            w (of class Symbol)
--      *     z (of class R)

i17 : stdio:332:3:(3): error: no method found for applying generators to:
     argument   :  I (of class Symbol)

i18 :       
R=ZZ/2[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;

      
i19 : 
o19 : Ideal of R

i20 : 
              1       4
o20 : Matrix R  <--- R

i21 :       
R=ZZ/2[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;
time LT=LyubeznikTable(I)
peek(LT)

      
i22 : 
o22 : Ideal of R

i23 : 
              1       4
o23 : Matrix R  <--- R

i24 :      -- used 0.174264 seconds

o24 = MutableHashTable{...1...}

o24 : MutableHashTable

i25 : 
o25 = MutableHashTable{(2, 2) => 1}

i26 :   pdim coker I      pdim coker I    

o26 = 3

i27 : dim coker I

o27 = 2

i28 : R=ZZ/2[x_1..x_3, y_1..y_3];

stdio:348:9:(3): error: no method for binary operator _ applied to objects:
--            x (of class R)
--      _     1 (of class ZZ)

i29 :       restart;


--loadPackage "TestIdeals"
--loadPackage "BinomialEdgeIdeals"


---load "~/Dropbox/Macaulay2/My Libraries/my PosChar July 2019.m2"
---load "~/Dropbox/Macaulay2/My Libraries/randomObjects.m2"




--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------
--                      F U N C T I O N S 
--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------

--The following raises an ideal/matrix to a Frobenius power;
frobeniusPowerX=method()

frobeniusPowerX(Ideal,ZZ) := (I1,e1) ->(
     R1:=ring I1;
     p1:=char R1;
     local answer;
     G1:=first entries gens I1;
     if (#G1==0) then answer=ideal(0_R1) else answer=ideal(apply(G1, j->j^(p1^e1)));
     answer
);



frobeniusPowerX(Matrix,ZZ) := (M,e) ->(
R:=ring M;
p:=char R;
G:=entries M;
local i;
local j;
L:={};
apply(G, i->
{
	L=append(L,apply(i, j->j^(p^e)));
});
matrix L
);


--- Given matrices A, B with target R^alpha find all v\in R^alpha such that B v \in Image A
--- by computing a kernel
matrixColon= (A, B) ->(
---t0:=cpuTime();
assert(target(A)==target(B));
m:=rank source B;
w:=map(coker A, source B, B);
answer:=gens kernel w;
---print(cpuTime()-t0);
answer
)


--- Given a generating morphism U:coker(A) -> F(coker A), compute a generating root U:coker(L) -> F(coker L)
generatingRoot= (A,U) ->(
	R:=ring(A);
	L:=A;
	alpha:=rank target A;
	LL:=transpose matrix{toList(alpha:0_R)};
	while ((( L)%( LL))!=0) do
	{
		LL=L;
		L=L | matrixColon(frobeniusPowerX(L,1),U);
		L=mingens image L;
---		print("=================================================================");
---		print(L);
	};
	L
)



---compute a generating morphism for H^(dim R -i)_I(R)
---the output is (A,U) where U:coker(A) -> F(coker A) is the generating morphism
generatingMorphism= (I,i) ->(
	R:=ring(I); p:=char(R);
	Ip:=gens frobeniusPowerX(ideal I,1);
	M:=coker I;
	Mp:=coker Ip;
---	resM:=res M;
---	resMp:=res Mp;
	f:=inducedMap(M,Mp);
	resf:=res f;
	E:=Ext^i(f, R^1);
	(source E, E)
)


MfilterSequence =(A,l)->
(
    local f; local  answer; local   counter; local r ;
    R := ring I;
    V:=ideal(vars(R));
    T:=target(A);
--    answer=findMaximalRegularSequence(gens I);
    answer={};
    while ((#answer)<l) do
    {
--       print(#answer);
       J:=ideal(append(answer,0_R));
       B:=J*T+image(A);
       f=false;
       counter=0;
       while (not f) do
       {
--	   print(counter);
	   if (counter<dim(R)) then
	       r=V_counter
	   else
               r=randomElementInIdeal(((counter-dim(R))//20),V);
	   c1:=gens (B:r);
--	   print("c1",c1);
	   c2:=prune subquotient(c1, gens B);
--	   print("c2",c2);
	   c3:=radical annihilator c2;
--	   print("c3",c3);
	   c4:=(gens(V))%(gens(c3));
--	   print("c4",c4);
	   f=(c4==0);
	   counter=counter+1;
       };
       answer=append(answer, r);
---       print("MfilterSequence",l,dim(R),counter,answer);
    };
    answer
)


randomElementInIdeal=(d,I)->
(
    local answer;
    R := ring I;
    g:=gens I;
    n:=rank source gens I;
    m:=random(R^{n:d},R^1);
--    print(m,g);
    answer=entries (g*m);
    answer=first first answer;
--    print (answer);
    answer
)

   

saturation=(J,f,N)->
(
J:f^N
)

limClosure =(G,n)->
(
    if ((#G)<n) then 
    {
	print (" *** FATAL ERROR *** LimClosure, sequence too short");
	return;
    };
    R :=ring (G#0);
    p:=char(R);
    genI:= apply(0..(n-1), i->G#i);
    J:=ideal(genI);
    P:=toList genI;
    PP:=product(P);
    lastJ:=ideal(genI);
    f:=true;
    while (f) do
    {
---print(mingens J);	
    	J=frobeniusPowerX(J,1);
--	apply(P, z-> {J=J:z});
--    	J=J:PP;
    	J=saturation(J,PP,p-1); J=substitute(J,R);
	f= (gens(J)%gens(lastJ))!=0;
	if (f) then
	{
	    lastJ=J;
        };
---    	print(f,J);
    };  
    J
)
---limClosure((x_{1,1},x_{1,2},x_{1,3}),2)
---time limClosure(G,h)


lowLimClosure =(G,n)->
(
    R :=ring (G#0); 
    if ((#G)<n) then 
    {
	print (" *** FATAL ERROR *** lowLimClosure, sequence too short");
	return;
    }
    else if (n==1) then 
    {
	return ideal(0_R);
    };
    LC:=limClosure(G,n-1);
    g:=G#(n-1);
    saturate(LC,g)
)

---------------------------------------------------------------------------------------------------
---load "~/Dropbox/Rodney/LClibNew.m2"

--- Given a generating morphism U:A/B -> F(A/B), compute a generating root U:coker(L) -> F(coker L)
--- A, B, U matrices with same target
generatingSubquotientRoot= (A,B,U) ->(
	R:=ring(A);
	B0:=B;
	Ap:=frobeniusPowerX(A,1);
	Bp:=frobeniusPowerX(B0,1);
	assert ((U*A)%(Ap)==0);
	assert ((U*B0)%(Bp)==0);
	B1:= matrixColon(Bp, U);
	B1=matrix entries B1;
	B1= gens (intersect(image(B1), image(A)));
	while ((B1%B0)!=0) do
	{
	    B0=B1;
	    Bp=frobeniusPowerX(B0,1);
	    B1= matrixColon(Bp, U);
	    B1=matrix entries B1;
	    B1= gens (intersect(image(B1), image(A)));
	};
    (A,B1,prune subquotient(A,B1))
)



Lyubeznik = (A,U,i) ->(
local t; local answer; local F; local  L0; local  L1; 
local f; local  g; local  h; local  B; local  V; local  C;
local X; local Y;
local W;
R:=ring (A);
p:=char(R);
T:=target(A);
if (i>0) then
{
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    Q:=prune subquotient(gens B, gens C);
    if (Q==0) then
    {
	answer=0;
    }
    else
    {
	(X,Y,W)=generatingSubquotientRoot (gens B, gens C,V);
	if (W==0) then
	{
	    answer=0;
	}
    	else
    	{
    	    G1:=Hom(coker vars(R), W); 
--    	    answer=length(G1);   --- fails if G1 is not graded
    	    answer=rank source mingens G1;   
	};
    };
};
------------------------------------
if (i==0) then
{
    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
	if (X==0) then
	{
	    answer=0;
	}
    	else
    	{
     	    G1:=Hom(coker vars(R),  W); 
--    	    answer=length(G1);  --- fails if G1 is not graded
    	    answer=rank source mingens G1;   
	};
};
answer
)

LyubeznikTable  = (I) ->
(
    local i;  local  j;
    answer := new MutableHashTable;
    d:=dim coker I;
    R := ring I;
    n:= dim R;
    for j from 0 to d do
    {
	E:=generatingMorphism(I,n-j);
	if (not ((E#1)==0)) then
	{
	    U:=matrix entries (E#1);
	    A:=relations E#0; A=matrix entries A;
	    G:=generatingRoot(A,U);
    	    for i from 0 to j do
    	    {
	     	Z:=Lyubeznik (G,U,i);
	     	if (Z>0) then answer#(i,j)=Z;
---		print("***",i,j,Z);
    	    };
	};
    };
answer
)











Macaulay2, version 1.19.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, InverseSystems, LLLBases, MinimalPrimes, PrimaryDecomposition, ReesAlgebra, Saturation, TangentCone

i1 :                                                                                                
o1 = frobeniusPowerX

o1 : MethodFunction

i2 :                                         
i3 :                                                                            
i4 :                                                             
o4 = matrixColon

o4 : FunctionClosure

i5 :                                                                                      
o5 = generatingRoot

o5 : FunctionClosure

i6 :                                                                                 
o6 = generatingMorphism

o6 : FunctionClosure

i7 :                                                                                                                                                                                                    
o7 = MfilterSequence

o7 : FunctionClosure

i8 :                                                                       
o8 = randomElementInIdeal

o8 : FunctionClosure

i9 :                               
o9 = saturation

o9 : FunctionClosure

i10 :                                                                                                                                                                                           
o10 = limClosure

o10 : FunctionClosure

i11 :                                                                                                                   
o11 = lowLimClosure

o11 : FunctionClosure

i12 :                                                                                                                                                       
o12 = generatingSubquotientRoot

o12 : FunctionClosure

i13 :                                                                                                                                                                                                                                                                                                                                                                                                                   stdio:295:13:(3): warning: local declaration of G1 shields variable with same name

o13 = Lyubeznik

o13 : FunctionClosure

i14 :                                                                                                                                                       
o14 = LyubeznikTable

o14 : FunctionClosure

i15 :                                                                   
R=ZZ/2[x_1..x_3, y_1..y_3];
I=ideal(x_1*y_2-x_2*y_1, x_1*y_3-x_3*y_1, x_3*y_2-x_2*y_3);
I=gens I;
time LT=LyubeznikTable(I)
peek(LT)

      
i16 : 
o16 : Ideal of R

i17 : 
              1       3
o17 : Matrix R  <--- R

i18 :      -- used 0.969932 seconds

o18 = MutableHashTable{...1...}

o18 : MutableHashTable

i19 : 
o19 = MutableHashTable{(4, 4) => 1}

i20 :     subsets(1..4, 2)      subsets(2, 1..4)  
stdio:346:5:(3): error: no method found for applying subsets to:
     argument 1 :  2 (of class ZZ)
     argument 2 :  (1, 2, 3, 4) (of class Sequence)

i21 :     subsets(1..4, 2)  

o21 = {{1, 2}, {1, 3}, {2, 3}, {1, 4}, {2, 4}, {3, 4}}

o21 : List

i22 : n=4;
R=ZZ/2[x_1..x_n, y_1..y_n];
I=apply(subsets(1..n, 2), s-> x_(s#0)*y_(s#1)-x_(s#1)*y_(s#2));


i23 : 
i24 : stdio:350:59:(3):[1]: error: array index 2 out of bounds 0 .. 1

i25 :       I=apply(subsets(1..n, 2), s-> x_(s#0)*y_(s#1)-x_(s#1)*y_(s#0));


i26 :       I

o26 = {x y  + x y , x y  + x y , x y  + x y , x y  + x y , x y  + x y , x y  + x y }
        2 1    1 2   3 1    1 3   3 2    2 3   4 1    1 4   4 2    2 4   4 3    3 4

o26 : List

i27 : I=gens ideal I;


              1       6
o27 : Matrix R  <--- R

i28 :       time LT=LyubeznikTable(I)
peek(LT)

     -- used 2.46145 seconds

o28 = MutableHashTable{...1...}

o28 : MutableHashTable

i29 : 
o29 = MutableHashTable{(5, 5) => 1}

i30 :       n=5;
R=ZZ/2[x_1..x_n, y_1..y_n];
I=apply(subsets(1..n, 2), s-> x_(s#0)*y_(s#1)-x_(s#1)*y_(s#0));
I=gens ideal I;
time LT=LyubeznikTable(I)
peek(LT)


i31 : 
i32 : 
i33 : 
              1       10
o33 : Matrix R  <--- R

i34 :      -- used 8.13297 seconds

o34 = MutableHashTable{...1...}

o34 : MutableHashTable

i35 : 
o35 = MutableHashTable{(6, 6) => 1}

i36 :       n=2;
R=ZZ/2[x_1..x_n, y_1..y_n];
I=apply(subsets(1..n, 2), s-> x_(s#0)*y_(s#1)-x_(s#1)*y_(s#0));
I=gens ideal I;
time LT=LyubeznikTable(I)
peek(LT)


i37 : 
i38 : 
i39 : 
              1       1
o39 : Matrix R  <--- R

i40 :      -- used 0.223545 seconds

o40 = MutableHashTable{...1...}

o40 : MutableHashTable

i41 : 
o41 = MutableHashTable{(3, 3) => 1}

i42 :       n=3;
R=ZZ/2[x_1..x_n, y_1..y_n];
I=apply(subsets(1..n, 2), s-> x_(s#0)*y_(s#1)-x_(s#1)*y_(s#0));
I=gens ideal I;
time LT=LyubeznikTable(I)
peek(LT)


i43 : 
i44 : 
i45 : 
              1       3
o45 : Matrix R  <--- R

i46 :      -- used 0.95198 seconds

o46 = MutableHashTable{...1...}

o46 : MutableHashTable

i47 : 
o47 = MutableHashTable{(4, 4) => 1}

i48 :       MfilterSequence (I,3)


o48 = {x , y , x  + x  + y }
        1   2   2    3    1

o48 : List

i49 :       E4=generatingMorphism(I,4)


o49 = (0, 0)

o49 : Sequence

i50 :       E4=generatingMorphism(I,0)


o50 = (image 0, 0)

o50 : Sequence

i51 :       E4=generatingMorphism(I,1)


o51 = (0, 0)

o51 : Sequence

i52 :       E4=generatingMorphism(I,2)


o52 = (cokernel {-3} | x_3 x_2 x_1 |, {-6} | x_2x_3y_1+x_1x_3y_2+x_1x_2y_3 x_1x_2x_3                     |)
                {-3} | y_3 y_2 y_1 |  {-6} | y_1y_2y_3                     x_3y_1y_2+x_2y_1y_3+x_1y_2y_3 |

o52 : Sequence

i53 :       A=matrix entries E4#0
U=matrix entries E4#1

stdio:391:10:(3):[1]: error: no method found for applying entries to:
     argument   :  cokernel {-3} | x_3 x_2 x_1 | (of class Module)
                            {-3} | y_3 y_2 y_1 |

i54 : 
o54 = | x_2x_3y_1+x_1x_3y_2+x_1x_2y_3 x_1x_2x_3                     |
      | y_1y_2y_3                     x_3y_1y_2+x_2y_1y_3+x_1y_2y_3 |

              2       2
o54 : Matrix R  <--- R

i55 :       A=matrix entries relations E4#0
U=matrix entries E4#1


o55 = | x_3 x_2 x_1 |
      | y_3 y_2 y_1 |

              2       3
o55 : Matrix R  <--- R

i56 : 
o56 = | x_2x_3y_1+x_1x_3y_2+x_1x_2y_3 x_1x_2x_3                     |
      | y_1y_2y_3                     x_3y_1y_2+x_2y_1y_3+x_1y_2y_3 |

              2       2
o56 : Matrix R  <--- R

i57 :       fs=MfilterSequence (A,3)


o57 = {x , y , x  + x  + y  + y  + y }
        1   2   2    3    1    2    3

o57 : List

i58 :       fs=MfilterSequence (A,3)


o58 = {x , y , x  + x  + y  + y  + y }
        1   2   2    3    1    2    3

o58 : List

i59 :       fs=MfilterSequence (A,3)


o59 = {x , y , x  + x  + y  + y  + y }
        1   2   1    2    1    2    3

o59 : List

i60 :       fs=MfilterSequence (A,3)


o60 = {x , y , x  + x  + y  + y }
        1   2   1    3    1    2

o60 : List

i61 :       fs=MfilterSequence (A,3)


o61 = {x , y , x  + x  + y  + y }
        1   2   1    3    2    3

o61 : List

i62 :       fs=MfilterSequence (A,3)


o62 = {x , y , x  + y }
        1   2   3    1

o62 : List

i63 :       F={x_1,y_2,x_3+y_1}


o63 = {x , y , x  + y }
        1   2   3    1

o63 : List

i64 :       i=0;
    L0=lowLimClosure(F,i)
    L1=lowLimClosure(F,i+1)


i65 : stdio:179:20:(3):[2]: error: expected matrices with the same target

i66 : 
o66 = ideal 0

o66 : Ideal of R

i67 :       E4=generatingMorphism(I,3)


o67 = (0, 0)

o67 : Sequence

i68 :       generatingMorphism(I,0)
generatingMorphism(I,1)
generatingMorphism(I,2)
generatingMorphism(I,3)
generatingMorphism(I,4)
generatingMorphism(I,5)
generatingMorphism(I,6)
generatingMorphism(I,7)


o68 = (image 0, 0)

o68 : Sequence

i69 : 
o69 = (0, 0)

o69 : Sequence

i70 : 
o70 = (cokernel {-3} | x_3 x_2 x_1 |, {-6} | x_2x_3y_1+x_1x_3y_2+x_1x_2y_3 x_1x_2x_3                     |)
                {-3} | y_3 y_2 y_1 |  {-6} | y_1y_2y_3                     x_3y_1y_2+x_2y_1y_3+x_1y_2y_3 |

o70 : Sequence

i71 : 
o71 = (0, 0)

o71 : Sequence

i72 : 
o72 = (0, 0)

o72 : Sequence

i73 : 
o73 = (0, 0)

o73 : Sequence

i74 : 
o74 = (0, 0)

o74 : Sequence

i75 : 
o75 = (0, 0)

o75 : Sequence

i76 :       for k from 0 to 2*n do
    print (k, prune Ext^k(coker I, R^1);

                  )
null
null
null
null
null
null
null

i77 : for k from 0 to 2*n do
    print (k, prune Ext^k(coker I, R^1));

      (0, 0)
(1, 0)
(2, cokernel {-3} | x_3 x_2 x_1 |)
             {-3} | y_3 y_2 y_1 |
(3, 0)
(4, 0)
(5, 0)
(6, 0)

i78 :       n=3;
R=QQ[x_1..x_n, y_1..y_n];
I=apply(subsets(1..n, 2), s-> x_(s#0)*y_(s#1)-x_(s#1)*y_(s#0));
I=gens ideal I;
for k from 0 to 2*n do
    print (k, prune Ext^k(coker I, R^1));
	


i79 : 
i80 : 
i81 : 
              1       3
o81 : Matrix R  <--- R

i82 :       (0, 0)
(1, 0)
(2, cokernel {-3} | x_3  x_2  x_1  |)
             {-3} | -y_3 -y_2 -y_1 |
(3, 0)
(4, 0)
(5, 0)
(6, 0)

i83 :             R=ZZ/2[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;
time LT=LyubeznikTable(I)
peek(LT)


i84 : 
o84 : Ideal of R

i85 : 
              1       4
o85 : Matrix R  <--- R

i86 :      -- used 0.173799 seconds

o86 = MutableHashTable{...1...}

o86 : MutableHashTable

i87 : 
o87 = MutableHashTable{(2, 2) => 1}

i88 :       generatingMorphism(I,0)
generatingMorphism(I,1)
generatingMorphism(I,2)
generatingMorphism(I,3)
generatingMorphism(I,4)
generatingMorphism(I,5)


o88 = (image 0, 0)

o88 : Sequence

i89 : 
o89 = (0, 0)

o89 : Sequence

i90 : 
o90 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o90 : Sequence

i91 : 
o91 = (cokernel {-5} | z y x w |, 0)

o91 : Sequence

i92 : 
o92 = (0, 0)

o92 : Sequence

i93 : 
o93 = (0, 0)

o93 : Sequence

i94 :       generatingMorphism(I,2)
generatingMorphism(I,3)


o94 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o94 : Sequence

i95 : 
o95 = (cokernel {-5} | z y x w |, 0)

o95 : Sequence

i96 :       R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;


i97 : 
o97 : Ideal of R

i98 : 
              1       4
o98 : Matrix R  <--- R

i99 :       generatingMorphism(I,2)
generatingMorphism(I,3)

stdio:89:12:(3):[1]: error: inducedMap: expected matrix to induce a well-defined map

i100 : stdio:89:12:(3):[1]: error: inducedMap: expected matrix to induce a well-defined map

i101 :        for k from 0 to 4 do
    print (k, prune Ext^k(coker I, R^1));

       (0, 0)
(1, 0)
(2, 0)
(3, cokernel {-6} | y w  0 x 0  0   0   0 0 |)
             {-6} | z -x y 0 w  0   2xz 0 0 |
             {-6} | 0 0  z y -x 2yz 0   0 0 |
             {-5} | 0 0  0 0 0  -z  -y  x w |
(4, cokernel {-7} | 0 0 0 0 z y x w |)
             {-8} | z y x w 0 0 0 0 |

i102 :        R=ZZ/2[w,x,y,z];


i103 :        for k from 0 to 4 do
    print (k, prune Ext^k(coker I, R^1));

       stdio:470:24:(3):[2]: error: expected modules over the same ring

i104 :        I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;

for k from 0 to 4 do
    print (k, prune Ext^k(coker I, R^1));


o104 : Ideal of R

i105 : 
               1       4
o105 : Matrix R  <--- R

i106 :               (0, 0)
(1, 0)
(2, cokernel {-3} | y w 0 x 0 |)
             {-3} | z x y 0 w |
             {-3} | 0 0 z y x |
(3, cokernel {-5} | z y x w |)
(4, 0)

i107 :        E2=generatingMorphism(I,2)
A=matrix entries E2#0
U=matrix entries relations E2#1

F=MfilterSequence (A,3)


o107 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o107 : Sequence

i108 : stdio:479:10:(3):[1]: error: no method found for applying entries to:
     argument   :  cokernel {-3} | y w 0 x 0 | (of class Module)
                            {-3} | z x y 0 w |
                            {-3} | 0 0 z y x |

i109 : stdio:480:18:(3):[1]: error: no method found for applying relations to:
     argument   :  {-6} | wxz    wxy     0       | (of class Matrix)
                   {-6} | wyz    x2z     x2y+wxz |
                   {-6} | y3+xz2 xyz+wz2 xy2+wyz |

i110 :        stdio:108:12:(3):[1]: error: expected ideal and module for the same ring

i111 :        R=ZZ/2[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;

for k from 0 to 4 do
    print (k, prune Ext^k(coker I, R^1));

time LT=LyubeznikTable(I)
peek(LT) -- only l(2,2)=1


i112 :        
o112 : Ideal of R

i113 : 
               1       4
o113 : Matrix R  <--- R

i114 :               (0, 0)
(1, 0)
(2, cokernel {-3} | y w 0 x 0 |)
             {-3} | z x y 0 w |
             {-3} | 0 0 z y x |
(3, cokernel {-5} | z y x w |)
(4, 0)

i115 :             -- used 0.16947 seconds

o115 = MutableHashTable{...1...}

o115 : MutableHashTable

i116 : 
o116 = MutableHashTable{(2, 2) => 1}

i117 :        E2=generatingMorphism(I,2)
A=matrix entries E2#0
U=matrix entries relations E2#1


o117 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o117 : Sequence

i118 : stdio:496:10:(3):[1]: error: no method found for applying entries to:
     argument   :  cokernel {-3} | y w 0 x 0 | (of class Module)
                            {-3} | z x y 0 w |
                            {-3} | 0 0 z y x |

i119 : stdio:497:18:(3):[1]: error: no method found for applying relations to:
     argument   :  {-6} | wxz    wxy     0       | (of class Matrix)
                   {-6} | wyz    x2z     x2y+wxz |
                   {-6} | y3+xz2 xyz+wz2 xy2+wyz |

i120 :        A=matrix entries relations E2#0
U=matrix entries E2#1


o120 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o120 : Matrix R  <--- R

i121 : 
o121 = | wxz    wxy     0       |
       | wyz    x2z     x2y+wxz |
       | y3+xz2 xyz+wz2 xy2+wyz |

               3       3
o121 : Matrix R  <--- R

i122 :        F=MfilterSequence (A,3)


o122 = {w, z, w}

o122 : List

i123 :        F=MfilterSequence (A,3)


o123 = {w, z, w}

o123 : List

i124 :        F=MfilterSequence (A,3)


o124 = {w, z, w}

o124 : List

i125 :        F=MfilterSequence (A,3)


o125 = {w, z, w}

o125 : List

i126 :        F=MfilterSequence (A,3)


o126 = {w, z, w}

o126 : List

i127 :        F=MfilterSequence (A,3)


o127 = {w, z, w}

o127 : List

i128 :        F=MfilterSequence (A,3)


o128 = {w, z, w}

o128 : List

i129 :        L1=lowLimClosure(F,1)


o129 = ideal 0

o129 : Ideal of R

i130 :        L0=lowLimClosure(F,0)

stdio:179:20:(3):[2]: error: expected matrices with the same target

i131 :        L2=lowLimClosure(F,2)


o131 = ideal w

o131 : Ideal of R

i132 :        L3=lowLimClosure(F,3)


o132 = ideal 1

o132 : Ideal of R

i133 :        
---F=MfilterSequence (A,3)
F={w,z,w};
L1=lowLimClosure(F,1)
L2=lowLimClosure(F,2)
L3=lowLimClosure(F,3)
f0=1_R;
f1=(F#0)^(p-1);
f2=f1*(F#1)^(p-1);
f2=f2*(F#2)^(p-1);

---------------------------------------------------------------------------
i=1;
g=F#i;
h=F#(i-1);
B=(L1*T+image(A)):g
V=f*U;
C=L0*T+h*T+image(A)


              
i134 : 
o134 = ideal 0

o134 : Ideal of R

i135 : 
o135 = ideal w

o135 : Ideal of R

i136 : 
o136 = ideal 1

o136 : Ideal of R

i137 : 
i138 : stdio:531:12:(3): error: no method for binary operator - applied to objects:
--            p (of class Symbol)
--      -     1 (of class ZZ)

i139 : stdio:532:15:(3): error: no method for binary operator - applied to objects:
--            p (of class Symbol)
--      -     1 (of class ZZ)

i140 : stdio:533:15:(3): error: no method for binary operator - applied to objects:
--            p (of class Symbol)
--      -     1 (of class ZZ)

i141 :               
i142 : 
i143 : 
i144 : stdio:539:6:(3): error: no method for binary operator * applied to objects:
--            ideal 0 (of class Ideal)
--      *     T (of class Symbol)

i145 : stdio:540:4:(3): error: no method for binary operator * applied to objects:
--            f (of class Symbol)
--      *     | wxz    wxy     0       | (of class Matrix)
--            | wyz    x2z     x2y+wxz |
--            | y3+xz2 xyz+wz2 xy2+wyz |

i146 : stdio:541:5:(3): error: no method for binary operator * applied to objects:
--            L0 (of class Symbol)
--      *     T (of class Symbol)

i147 :               p=2;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;


i148 : 
i149 :        
o149 : Ideal of R

i150 : 
               1       4
o150 : Matrix R  <--- R

i151 :        E2=generatingMorphism(I,2)


o151 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o151 : Sequence

i152 :        g=F#1;
h=F#0;
B=(L1*T+image(A)):g


i153 : 
i154 : stdio:554:6:(3): error: no method for binary operator * applied to objects:
--            ideal 0 (of class Ideal)
--      *     T (of class Symbol)

i155 :        T=target A


        ZZ       3
o155 = (--[w..z])
         2

       ZZ
o155 : --[w..z]-module, free
        2

i156 :        B=(L1*T+image(A)):g
V=f*U;
C=L0*T+h*T+image(A)


o156 = image | y w 0 x 0 |
             | z x y 0 w |
             | 0 0 z y x |

       ZZ                             ZZ       3
o156 : --[w..z]-module, submodule of (--[w..z])
        2                              2

i157 : stdio:559:4:(3): error: no method for binary operator * applied to objects:
--            f (of class Symbol)
--      *     | wxz    wxy     0       | (of class Matrix)
--            | wyz    x2z     x2y+wxz |
--            | y3+xz2 xyz+wz2 xy2+wyz |

i158 : stdio:560:5:(3): error: no method for binary operator * applied to objects:
--            L0 (of class Symbol)
--             ZZ       3
--      *     (--[w..z])  (of class Module)
--              2

i159 :        g=F#1;
h=F#0;
B=(L1*T+image(A)):g
V=f1*U;
C=L0*T+h*T+image(A)


i160 : 
i161 : 
o161 = image | y w 0 x 0 |
             | z x y 0 w |
             | 0 0 z y x |

       ZZ                             ZZ       3
o161 : --[w..z]-module, submodule of (--[w..z])
        2                              2

i162 : stdio:565:5:(3): error: no method for binary operator * applied to objects:
--            f1 (of class Symbol)
--      *     | wxz    wxy     0       | (of class Matrix)
--            | wyz    x2z     x2y+wxz |
--            | y3+xz2 xyz+wz2 xy2+wyz |

i163 : stdio:566:5:(3): error: no method for binary operator * applied to objects:
--            L0 (of class Symbol)
--             ZZ       3
--      *     (--[w..z])  (of class Module)
--              2

i164 :        B=(L1*T+image(A)):g


o164 = image | y w 0 x 0 |
             | z x y 0 w |
             | 0 0 z y x |

       ZZ                             ZZ       3
o164 : --[w..z]-module, submodule of (--[w..z])
        2                              2

i165 :        B=(L1*T+image(A)):g
V=f1*U;


o165 = image | y w 0 x 0 |
             | z x y 0 w |
             | 0 0 z y x |

       ZZ                             ZZ       3
o165 : --[w..z]-module, submodule of (--[w..z])
        2                              2

i166 : stdio:571:5:(3): error: no method for binary operator * applied to objects:
--            f1 (of class Symbol)
--      *     | wxz    wxy     0       | (of class Matrix)
--            | wyz    x2z     x2y+wxz |
--            | y3+xz2 xyz+wz2 xy2+wyz |

i167 :        F={w,z,w};
L1=lowLimClosure(F,1)
L2=lowLimClosure(F,2)
L3=lowLimClosure(F,3)
f0=1_R;
f1=(F#0)^(p-1);
f2=f1*(F#1)^(p-1);
f2=f2*(F#2)^(p-1);


i168 : 
o168 = ideal 0

o168 : Ideal of R

i169 : 
o169 = ideal w

o169 : Ideal of R

i170 : 
o170 = ideal 1

o170 : Ideal of R

i171 : 
i172 : 
i173 : 
i174 : 
i175 :        V=f1*U;

stdio:582:5:(3): error: no method found for applying promote to:
     argument 1 :  w (of class R)
                   ZZ
     argument 2 :  --[w..z]
                    2

i176 :        p=2;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;

for k from 0 to 4 do
    print (k, prune Ext^k(coker I, R^1));

time LT=LyubeznikTable(I)
peek(LT) -- only l(2,2)=1

E2=generatingMorphism(I,2)
A=matrix entries relations E2#0
T=target A
U=matrix entries E2#1

---F=MfilterSequence (A,3)
F={w,z,w};
L1=lowLimClosure(F,1)
L2=lowLimClosure(F,2)
L3=lowLimClosure(F,3)
f0=1_R;
f1=(F#0)^(p-1);
f2=f1*(F#1)^(p-1);
f2=f2*(F#2)^(p-1);

---------------------------------------------------------------------------
-------------- i=1
---------------------------------------------------------------------------
g=F#1;
h=F#0;
B=(L1*T+image(A)):g
V=f1*U;


i177 : 
i178 :        
o178 : Ideal of R

i179 : 
               1       4
o179 : Matrix R  <--- R

i180 :               (0, 0)
(1, 0)
(2, cokernel {-3} | y w 0 x 0 |)
             {-3} | z x y 0 w |
             {-3} | 0 0 z y x |
(3, cokernel {-5} | z y x w |)
(4, 0)

i181 :             -- used 0.173326 seconds

o181 = MutableHashTable{...1...}

o181 : MutableHashTable

i182 : 
o182 = MutableHashTable{(2, 2) => 1}

i183 :        
o183 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o183 : Sequence

i184 : 
o184 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o184 : Matrix R  <--- R

i185 : 
        3
o185 = R

o185 : R-module, free

i186 : 
o186 = | wxz    wxy     0       |
       | wyz    x2z     x2y+wxz |
       | y3+xz2 xyz+wz2 xy2+wyz |

               3       3
o186 : Matrix R  <--- R

i187 :               
i188 : 
o188 = ideal 0

o188 : Ideal of R

i189 : 
o189 = ideal w

o189 : Ideal of R

i190 : 
o190 = ideal 1

o190 : Ideal of R

i191 : 
i192 : 
i193 : 
i194 : 
i195 :                             
i196 : 
i197 : 
o197 = image | y w 0 x 0 |
             | z x y 0 w |
             | 0 0 z y x |

                               3
o197 : R-module, submodule of R

i198 : 
               3       3
o198 : Matrix R  <--- R

i199 :        p=2;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;

for k from 0 to 4 do
    print (k, prune Ext^k(coker I, R^1));

time LT=LyubeznikTable(I)
peek(LT) -- only l(2,2)=1

E2=generatingMorphism(I,2)
A=matrix entries relations E2#0
T=target A
U=matrix entries E2#1

---F=MfilterSequence (A,3)
F={w,z,w};
L1=lowLimClosure(F,1)
L2=lowLimClosure(F,2)
L3=lowLimClosure(F,3)
f0=1_R;
f1=(F#0)^(p-1);
f2=f1*(F#1)^(p-1);
f2=f2*(F#2)^(p-1);

---------------------------------------------------------------------------
-------------- i=1
---------------------------------------------------------------------------
g=F#1;
h=F#0;
B=(L1*T+image(A)):g
V=f1*U;
C=L0*T+h*T+image(A)


i200 : 
i201 :        
o201 : Ideal of R

i202 : 
               1       4
o202 : Matrix R  <--- R

i203 :               (0, 0)
(1, 0)
(2, cokernel {-3} | y w 0 x 0 |)
             {-3} | z x y 0 w |
             {-3} | 0 0 z y x |
(3, cokernel {-5} | z y x w |)
(4, 0)

i204 :             -- used 0.170806 seconds

o204 = MutableHashTable{...1...}

o204 : MutableHashTable

i205 : 
o205 = MutableHashTable{(2, 2) => 1}

i206 :        
o206 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o206 : Sequence

i207 : 
o207 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o207 : Matrix R  <--- R

i208 : 
        3
o208 = R

o208 : R-module, free

i209 : 
o209 = | wxz    wxy     0       |
       | wyz    x2z     x2y+wxz |
       | y3+xz2 xyz+wz2 xy2+wyz |

               3       3
o209 : Matrix R  <--- R

i210 :               
i211 : 
o211 = ideal 0

o211 : Ideal of R

i212 : 
o212 = ideal w

o212 : Ideal of R

i213 : 
o213 = ideal 1

o213 : Ideal of R

i214 : 
i215 : 
i216 : 
i217 : 
i218 :                             
i219 : 
i220 : 
o220 = image | y w 0 x 0 |
             | z x y 0 w |
             | 0 0 z y x |

                               3
o220 : R-module, submodule of R

i221 : 
               3       3
o221 : Matrix R  <--- R

i222 : stdio:653:5:(3): error: no method for binary operator * applied to objects:
--            L0 (of class Symbol)
--             3
--      *     R  (of class Module)

i223 :        L0=ideal(0_R)


o223 = ideal 0

o223 : Ideal of R

i224 :        C=L0*T+h*T+image(A)


o224 = image | 0 0 0 w 0 0 y w 0 x 0 |
             | 0 0 0 0 w 0 z x y 0 w |
             | 0 0 0 0 0 w 0 0 z y x |

                               3
o224 : R-module, submodule of R

i225 :        	C0=gens C;
	Bp=frobeniusPowerX(gens B,1);
	Cp=frobeniusPowerX(C0,1);


               3       11
o225 : Matrix R  <--- R

i226 : 
               3       5
o226 : Matrix R  <--- R

i227 : 
               3       11
o227 : Matrix R  <--- R

i228 :        	C0=gens C;
	Bp=frobeniusPowerX(gens B,1);
	Cp=frobeniusPowerX(C0,1);
	assert ((V*(gens B))%(Bp)==0);


               3       11
o228 : Matrix R  <--- R

i229 : 
               3       5
o229 : Matrix R  <--- R

i230 : 
               3       11
o230 : Matrix R  <--- R

i231 : 
i232 :        	assert ((V*C0)%(Cp)==0);


i233 :        	assert ((V*C0)%(Cp)==0);
	C1= matrixColon(Cp, V);
	C1=matrix entries C1;
	C1= gens (intersect(image(C1), B));


i234 : 
               3       8
o234 : Matrix R  <--- R

i235 : 
               3       8
o235 : Matrix R  <--- R

i236 : 
               3       5
o236 : Matrix R  <--- R

i237 :        	assert ((V*C0)%(Cp)==0);
	C1= matrixColon(Cp, V);
	C1=matrix entries C1;
	C1= gens (intersect(image(C1), B));
	print ((C1%C0)==0);  -- C1==C0 so we  stabilized


i238 : 
               3       8
o238 : Matrix R  <--- R

i239 : 
               3       8
o239 : Matrix R  <--- R

i240 : 
               3       5
o240 : Matrix R  <--- R

i241 : true

i242 :      C0       C0  

o242 = | 0 0 0 w 0 0 y w 0 x 0 |
       | 0 0 0 0 w 0 z x y 0 w |
       | 0 0 0 0 0 w 0 0 z y x |

               3       11
o242 : Matrix R  <--- R

i243 : peek(LT)

o243 = MutableHashTable{(2, 2) => 1}

i244 : g=F#2;
h=F#1;
B=(L2*T+image(A)):g
V=f2*U;
C=L0*T+h*T+image(A)

	C0=gens C;
	Bp=frobeniusPowerX(gens B,1);
	Cp=frobeniusPowerX(C0,1);
	assert ((V*(gens B))%(Bp)==0);
	assert ((V*C0)%(Cp)==0);
	C1= matrixColon(Cp, V);
	C1=matrix entries C1;
	C1= gens (intersect(image(C1), B));
	print ((C1%C0)==0);  -- C1==C0 so we  stabilized


i245 : 
i246 : 
        3
o246 = R

o246 : R-module, free

i247 : 
               3       3
o247 : Matrix R  <--- R

i248 : 
o248 = image | 0 0 0 z 0 0 y w 0 x 0 |
             | 0 0 0 0 z 0 z x y 0 w |
             | 0 0 0 0 0 z 0 0 z y x |

                               3
o248 : R-module, submodule of R

i249 :        
               3       11
o249 : Matrix R  <--- R

i250 : 
               3       3
o250 : Matrix R  <--- R

i251 : 
               3       11
o251 : Matrix R  <--- R

i252 : 
i253 : 
i254 : 
               3       10
o254 : Matrix R  <--- R

i255 : 
               3       10
o255 : Matrix R  <--- R

i256 : 
               3       8
o256 : Matrix R  <--- R

i257 : true

i258 :        C0

o258 = | 0 0 0 z 0 0 y w 0 x 0 |
       | 0 0 0 0 z 0 z x y 0 w |
       | 0 0 0 0 0 z 0 0 z y x |

               3       11
o258 : Matrix R  <--- R

i259 : f3=f3*(F#2)^(p-1);

stdio:700:6:(3): error: no method for binary operator * applied to objects:
--            f3 (of class Symbol)
--      *     w (of class R)

i260 :        f3=f2*(F#2)^(p-1);


i261 :        F

o261 = {w, z, w}

o261 : List

i262 : g=F#0;
h=0;
B=(L0*T+image(A)):g
V=f1*U;
C=L0*T+h*T+image(A)


i263 : 
i264 : 
o264 = image | y w 0 x 0 |
             | z x y 0 w |
             | 0 0 z y x |

                               3
o264 : R-module, submodule of R

i265 : 
               3       3
o265 : Matrix R  <--- R

i266 : 
o266 = image | 0 0 0 0 0 0 y w 0 x 0 |
             | 0 0 0 0 0 0 z x y 0 w |
             | 0 0 0 0 0 0 0 0 z y x |

                               3
o266 : R-module, submodule of R

i267 :        	C0=gens C;
	Bp=frobeniusPowerX(gens B,1);
	Cp=frobeniusPowerX(C0,1);
	assert ((V*(gens B))%(Bp)==0);
	assert ((V*C0)%(Cp)==0);
	C1= matrixColon(Cp, V);
	C1=matrix entries C1;
	C1= gens (intersect(image(C1), B));
	print ((C1%C0)==0);  -- C1==C0 so we  stabilized


               3       11
o267 : Matrix R  <--- R

i268 : 
               3       5
o268 : Matrix R  <--- R

i269 : 
               3       11
o269 : Matrix R  <--- R

i270 : 
i271 : 
i272 : 
               3       8
o272 : Matrix R  <--- R

i273 : 
               3       8
o273 : Matrix R  <--- R

i274 : 
               3       5
o274 : Matrix R  <--- R

i275 : true

i276 :     C1       C1   

o276 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o276 : Matrix R  <--- R

i277 : lowLimClosure(F,3)
stdio:179:20:(3):[2]: error: expected matrices with the same target

i278 : lowLimClosure(F,1)

o278 = ideal 0

o278 : Ideal of R

i279 : lowLimClosure(F,2)

o279 = ideal w

o279 : Ideal of R

i280 : lowLimClosure(F,3)

o280 = ideal 1

o280 : Ideal of R

i281 : i=0

    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;


o281 = 0

i282 :        
i283 : 
o283 : Ideal of R

i284 : 
o284 : Ideal of R

i285 : 
i286 : 
i287 : 
i288 : 
i289 :        i=0

    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);


o289 = 0

i290 :        
i291 : 
o291 : Ideal of R

i292 : 
o292 : Ideal of R

i293 : 
i294 : 
i295 : 
i296 : 
i297 : 
               3       3
o297 : Matrix R  <--- R

i298 : 
i299 :        i=0

    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);


o299 = 0

i300 :        
i301 : 
o301 : Ideal of R

i302 : 
o302 : Ideal of R

i303 : 
i304 : 
i305 : 
i306 : 
i307 : 
               3       3
o307 : Matrix R  <--- R

i308 : 
i309 : 
i310 :        X

o310 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o310 : Matrix R  <--- R

i311 : 	if (X==0) then
	{
	    answer=0;
	}
    	else
    	{
     	    G1:=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
	};

                     
i312 : stdio:766:9:(3): error: syntax error at 'else'

i312 :                      
i313 :        	if (X==0) then
	{
	    answer=0;
	}
    	else
    	{
     	    G1:=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
	};

                     
i314 : stdio:775:9:(3): error: syntax error at 'else'

i314 :                      stdio:776:13:(3): warning: local declaration of G1 shields variable with same name

i315 :        G1

o315 = 0

o315 : R-module

i316 : i=1;
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    Q:=prune subquotient(gens B, gens C);
    if (Q==0) then
    {
	answer=0;
    }
    else
    {
	(X,Y,W)=generatingSubquotientRoot (gens B, gens C,V);
	if (W==0) then
	{
	    answer=0;
	}
    	else
    	{
    	    G1:=Hom(coker vars(R), W); 
--    	    answer=length(G1);   --- fails if G1 is not graded
    	    answer=rank source mingens G1;   
	};
    };


i317 : 
i318 : 
o318 : Ideal of R

i319 : 
o319 : Ideal of R

i320 : 
i321 : 
i322 : 
i323 : 
i324 : 
               3       3
o324 : Matrix R  <--- R

i325 : 
i326 : 
i327 :                      
o327 = {}

o327 : List

i328 : stdio:796:5:(3): error: syntax error at 'else'

i328 :                                                                                     stdio:804:13:(3): warning: local declaration of G1 shields variable with same name

i329 :        

i=1;
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    Q:=prune subquotient(gens B, gens C);
    if (Q==0) then
    {
	answer=0;
    }
    else
    {
	(X,Y,W)=generatingSubquotientRoot (gens B, gens C,V);
	if (W==0) then
	{
	    answer=0;
	}
    	else
    	{
    	    G1:=Hom(coker vars(R), W); 
    	    answer=rank source mingens G1;   
	};
    };



              
i330 : 
i331 : 
o331 : Ideal of R

i332 : 
o332 : Ideal of R

i333 : 
i334 : 
i335 : 
i336 : 
i337 : 
               3       3
o337 : Matrix R  <--- R

i338 : 
i339 : stdio:822:5:(3): warning: local declaration of Q shields variable with same name

i340 :                      
o340 = {}

o340 : List

i341 : stdio:827:5:(3): error: syntax error at 'else'

i341 :                                                                              stdio:835:13:(3): warning: local declaration of G1 shields variable with same name

i342 :                          F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    Q:=prune subquotient(gens B, gens C);


i343 : 
o343 : Ideal of R

i344 : 
o344 : Ideal of R

i345 : 
i346 : 
i347 : 
i348 : 
i349 : 
               3       3
o349 : Matrix R  <--- R

i350 : 
i351 : stdio:851:5:(3): warning: local declaration of Q shields variable with same name

i352 :            Q=prune subquotient(gens B, gens C);


i353 :            Q=prune subquotient(gens B, gens C);
    if (Q==0) then
    {
	answer=0;
    }


i354 :                      
o354 = {}

o354 : List

i355 :            {
	(X,Y,W)=generatingSubquotientRoot (gens B, gens C,V);
	if (W==0) then
	{
	    answer=0;
	}
    	else
    	{
    	    G1:=Hom(coker vars(R), W); 
    	    answer=rank source mingens G1;   
	};
    };

                                                                             stdio:869:13:(3): warning: local declaration of G1 shields variable with same name

i356 :       Q==0       Q==0 

o356 = true

i357 : i=1;
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    Q=prune subquotient(gens B, gens C);
    assert (Q==0);
    answer=0;


i358 : 
i359 : 
o359 : Ideal of R

i360 : 
o360 : Ideal of R

i361 : 
i362 : 
i363 : 
i364 : 
i365 : 
               3       3
o365 : Matrix R  <--- R

i366 : 
i367 : 
i368 : 
i369 : 
i370 :        i=2;
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    Q=prune subquotient(gens B, gens C);


i371 : 
i372 : 
o372 : Ideal of R

i373 : 
o373 : Ideal of R

i374 : 
i375 : 
i376 : 
i377 : 
i378 : 
               3       3
o378 : Matrix R  <--- R

i379 : 
i380 : 
i381 :        Q

o381 = cokernel | z y w 0 0 0 0 0 x 0 0 |
                | 0 0 0 z y x w 0 0 0 0 |
                | 0 0 0 0 0 0 0 z y x w |

                              3
o381 : R-module, quotient of R

i382 :     if (Q==0) then
    {
	answer=0;
    }
    else
    {
	(X,Y,W)=generatingSubquotientRoot (gens B, gens C,V);
	if (W==0) then
	{
	    answer=0;
	}
    	else
    	{
    	    G1:=Hom(coker vars(R), W); 
    	    answer=rank source mingens G1;   
	};
    };

                     
i383 : stdio:906:5:(3): error: syntax error at 'else'

i383 :                                                                              stdio:914:13:(3): warning: local declaration of G1 shields variable with same name

i384 :            if (Q==0) then
    {
	answer=0;
    }

                     
i385 :            {
	(X,Y,W)=generatingSubquotientRoot (gens B, gens C,V);
	if (W==0) then
	{
	    answer=0;
	}
    	else
    	{
    	    G1:=Hom(coker vars(R), W); 
    	    answer=rank source mingens G1;   
	};
    };


                                                                             stdio:932:13:(3): warning: local declaration of G1 shields variable with same name

i386 :        answer              answer       

o386 = 1

i387 : ------------------------------------
i=0

    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
	if (X==0) then
	{
	    answer=0;
	}
    	else
    	{
     	    G1:=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
	};



       
o387 = 0

i388 :        
i389 : 
o389 : Ideal of R

i390 : 
o390 : Ideal of R

i391 : 
i392 : 
i393 : 
i394 : 
i395 : 
               3       3
o395 : Matrix R  <--- R

i396 : 
i397 : 
i398 :                      
i399 : stdio:956:9:(3): error: syntax error at 'else'

i399 :                      stdio:957:13:(3): warning: local declaration of G1 shields variable with same name

i400 :           X                     X           

o400 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o400 : Matrix R  <--- R

i401 : answer

o401 = 0

i402 : W

o402 = 0

o402 : R-module

i403 : C

o403 = image | 0 0 0 0 0 0 y w 0 x 0 |
             | 0 0 0 0 0 0 z x y 0 w |
             | 0 0 0 0 0 0 0 0 z y x |

                               3
o403 : R-module, submodule of R

i404 : V

o404 = | wxz    wxy     0       |
       | wyz    x2z     x2y+wxz |
       | y3+xz2 xyz+wz2 xy2+wyz |

               3       3
o404 : Matrix R  <--- R

i405 : C

o405 = image | 0 0 0 0 0 0 y w 0 x 0 |
             | 0 0 0 0 0 0 z x y 0 w |
             | 0 0 0 0 0 0 0 0 z y x |

                               3
o405 : R-module, submodule of R

i406 : X

o406 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o406 : Matrix R  <--- R

i407 :     prune subquotient (gens B, gens C)


o407 = 0

o407 : R-module

i408 :            print(answer, prune subquotient (gens B, gens C));

(0, 0)

i409 :        i=1;
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    print(answer, prune subquotient (gens B, gens C));


i410 : 
i411 : 
o411 : Ideal of R

i412 : 
o412 : Ideal of R

i413 : 
i414 : 
i415 : 
i416 : 
i417 : 
               3       3
o417 : Matrix R  <--- R

i418 : 
i419 : (0, 0)

i420 :        i=2;
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    Q=prune subquotient(gens B, gens C);


i421 : 
i422 : 
o422 : Ideal of R

i423 : 
o423 : Ideal of R

i424 : 
i425 : 
i426 : 
i427 : 
i428 : 
               3       3
o428 : Matrix R  <--- R

i429 : 
i430 : 
i431 :            print(answer, prune subquotient (gens B, gens C));

(0, cokernel | z y w 0 0 0 0 0 x 0 0 |)
             | 0 0 0 z y x w 0 0 0 0 |
             | 0 0 0 0 0 0 0 z y x w |

i432 :            if (Q==0) then
    {
	answer=0;
    }

                     
i433 :        Q

o433 = cokernel | z y w 0 0 0 0 0 x 0 0 |
                | 0 0 0 z y x w 0 0 0 0 |
                | 0 0 0 0 0 0 0 z y x w |

                              3
o433 : R-module, quotient of R

i434 :    {
	(X,Y,W)=generatingSubquotientRoot (gens B, gens C,V);
	if (W==0) then
	{
	    answer=0;
	}
    	else
    	{
    	    G1=Hom(coker vars(R), W); 
    	    answer=rank source mingens G1;   
	};
    };
    print(answer, prune subquotient (gens B, gens C));

                                                                             
i435 : (1, cokernel | z y w 0 0 0 0 0 x 0 0 |)
             | 0 0 0 z y x w 0 0 0 0 |
             | 0 0 0 0 0 0 0 z y x w |

i436 :       X       X 

o436 = | 1 0 0 |
       | 0 1 0 |
       | 0 0 1 |

               3       3
o436 : Matrix R  <--- R

i437 : Y

o437 = | 0 z y w 0 x 0 0 |
       | 1 0 0 0 0 0 0 0 |
       | 0 0 0 0 z y x w |

               3       8
o437 : Matrix R  <--- R

i438 : W

o438 = cokernel | z y w 0 x 0 0 |
                | 0 0 0 z y x w |

                              2
o438 : R-module, quotient of R

i439 :     	    G1=Hom(coker vars(R), W); 


i440 :        G

o440 = G

o440 : Symbol

i441 : G1

o441 = subquotient (| x |, | z y w 0 x 0 0 |)
                    | 0 |  | 0 0 0 z y x w |

                                 2
o441 : R-module, subquotient of R

i442 : 

i=1;
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    print(answer, prune subquotient (gens B, gens C));

              
i443 : 
i444 : 
o444 : Ideal of R

i445 : 
o445 : Ideal of R

i446 : 
i447 : 
i448 : 
i449 : 
i450 : 
               3       3
o450 : Matrix R  <--- R

i451 : 
i452 : (1, 0)

i453 :        i=1;
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    print(prune subquotient (gens B, gens C));


i454 : 
i455 : 
o455 : Ideal of R

i456 : 
o456 : Ideal of R

i457 : 
i458 : 
i459 : 
i460 : 
i461 : 
               3       3
o461 : Matrix R  <--- R

i462 : 
i463 : 0

i464 :      B       B  

o464 = image | w y 0 0 0 x 0 0 |
             | 0 z x w y 0 0 0 |
             | 0 0 0 0 z y x w |

                               3
o464 : R-module, submodule of R

i465 : C

o465 = image | 0 0 0 w 0 0 y w 0 x 0 |
             | 0 0 0 0 w 0 z x y 0 w |
             | 0 0 0 0 0 w 0 0 z y x |

                               3
o465 : R-module, submodule of R

i466 : mingens C

o466 = | w y 0 0 0 x 0 0 |
       | 0 z x w y 0 0 0 |
       | 0 0 0 0 z y x w |

               3       8
o466 : Matrix R  <--- R

i467 : 

E3=generatingMorphism(I,3)
A=matrix entries relations E3#0
T=target A
U=matrix entries E3#1


              
o467 = (cokernel {-5} | z y x w |, 0)

o467 : Sequence

i468 : 
o468 = | z y x w |

               1       4
o468 : Matrix R  <--- R

i469 : 
        1
o469 = R

o469 : R-module, free

i470 : 
o470 = 0

               1       1
o470 : Matrix R  <--- R

i471 :               A

o471 = | z y x w |

               1       4
o471 : Matrix R  <--- R

i472 : T

        1
o472 = R

o472 : R-module, free

i473 : U

o473 = 0

               1       1
o473 : Matrix R  <--- R

i474 : p=2;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;

for k from 0 to 4 do
    print (k, prune Ext^k(coker I, R^1));


i475 : 
i476 :        
o476 : Ideal of R

i477 : 
               1       4
o477 : Matrix R  <--- R

i478 :               (0, 0)
(1, 0)
(2, cokernel {-3} | y w 0 x 0 |)
             {-3} | z x y 0 w |
             {-3} | 0 0 z y x |
(3, cokernel {-5} | z y x w |)
(4, 0)

i479 :        p=2;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;

for k from 0 to 4 do
    print (k, prune Ext^k(coker I, R^1));


i480 : 
i481 :        
o481 : Ideal of R

i482 : 
               1       4
o482 : Matrix R  <--- R

i483 :               (0, 0)
(1, 0)
(2, cokernel {-3} | y w 0 x 0 |)
             {-3} | z x y 0 w |
             {-3} | 0 0 z y x |
(3, cokernel {-5} | z y x w |)
(4, 0)

i484 :        E2=generatingMorphism(I,2)


o484 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o484 : Sequence

i485 :        E0=generatingMorphism(I,0)


o485 = (image 0, 0)

o485 : Sequence

i486 :        E1=generatingMorphism(I,1)


o486 = (0, 0)

o486 : Sequence

i487 :        E2=generatingMorphism(I,2)


o487 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o487 : Sequence

i488 :        E2=generatingMorphism(I,2)
E3=generatingMorphism(I,3)


o488 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o488 : Sequence

i489 : 
o489 = (cokernel {-5} | z y x w |, 0)

o489 : Sequence

i490 :        E2=generatingMorphism(I,2)
E3=generatingMorphism(I,3)
E4=generatingMorphism(I,4)


o490 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o490 : Sequence

i491 : 
o491 = (cokernel {-5} | z y x w |, 0)

o491 : Sequence

i492 : 
o492 = (0, 0)

o492 : Sequence

i493 :            F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    -- im B = im C!
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
	if (X==0) then
	{
	    answer=0;
	}
    	else
    	{
     	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
	};
    print(answer, prune subquotient (gens B, gens C));

stdio:108:12:(3):[1]: error: expected ideal and module for the same ring

i494 : 
o494 : Ideal of R

i495 : 
o495 : Ideal of R

i496 : 
i497 : 
i498 : 
i499 : stdio:1106:10:(3): error: expected ideal and module for the same ring

i500 : stdio:1107:8:(3): error: no method found for applying promote to:
     argument 1 :  1 (of class R)
                   ZZ
     argument 2 :  --[w..z]
                    2

i501 : stdio:1108:9:(3): error: expected ideal and module for the same ring

i502 :        
i503 :                      
i504 : stdio:1115:9:(3): error: syntax error at 'else'

i504 :                      stdio:1116:16:(3): error: expected compatible rings

i505 : (1, 0)

i506 :        E2=generatingMorphism(I,2)
A=matrix entries relations E2#0
T=target A
U=matrix entries E2#1


o506 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o506 : Sequence

i507 : 
o507 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o507 : Matrix R  <--- R

i508 : 
        3
o508 = R

o508 : R-module, free

i509 : 
o509 = | wxz    wxy     0       |
       | wyz    x2z     x2y+wxz |
       | y3+xz2 xyz+wz2 xy2+wyz |

               3       3
o509 : Matrix R  <--- R

i510 :        i=0

    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);


o510 = 0

i511 :        
i512 : 
o512 : Ideal of R

i513 : 
o513 : Ideal of R

i514 :        i=0

    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);


o514 = 0

i515 :        
i516 : 
o516 : Ideal of R

i517 : 
o517 : Ideal of R

i518 : 
i519 : 
i520 : 
i521 : 
i522 : 
               3       3
o522 : Matrix R  <--- R

i523 : 
i524 :        i=0

    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    -- im B = im C!
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);


o524 = 0

i525 :        
i526 : 
o526 : Ideal of R

i527 : 
o527 : Ideal of R

i528 : 
i529 : 
i530 : 
i531 : 
i532 : 
               3       3
o532 : Matrix R  <--- R

i533 : 
i534 :        
i535 :        i=0

    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    -- im B = im C!
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
	if (X==0) then
	{
	    answer=0;
	}
    	else
    	{
     	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
	};


o535 = 0

i536 :        
i537 : 
o537 : Ideal of R

i538 : 
o538 : Ideal of R

i539 : 
i540 : 
i541 : 
i542 : 
i543 : 
               3       3
o543 : Matrix R  <--- R

i544 : 
i545 :        
i546 :                      
i547 : stdio:1175:9:(3): error: syntax error at 'else'

i547 :                      
i548 :        X

o548 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o548 : Matrix R  <--- R

i549 : assert (X!=0);


i550 :        assert (X!=0);
     	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   


i551 : 
i552 : 
i553 :        	};

stdio:1187:9:(3): error: syntax error at '}'

i553 :            print(answer, prune subquotient (gens B, gens C));

(0, 0)

i554 :        i=1;
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));


i555 : 
i556 : 
o556 : Ideal of R

i557 : 
o557 : Ideal of R

i558 : 
i559 :        i=1;
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    print(prune subquotient (gens B, gens C));


i560 : 
i561 : 
o561 : Ideal of R

i562 : 
o562 : Ideal of R

i563 : 
i564 : 
i565 : 
i566 : 
i567 : 
               3       3
o567 : Matrix R  <--- R

i568 : 
i569 : 0

i570 :        E3=generatingMorphism(I,2)
A=matrix entries relations E3#0
T=target A
U=matrix entries E3#1


------------------------------------
i=0

    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    -- im B = im C!
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
assert (X!=0);
     	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
    print(answer, prune subquotient (gens B, gens C));
    


o570 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o570 : Sequence

i571 : 
o571 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o571 : Matrix R  <--- R

i572 : 
        3
o572 = R

o572 : R-module, free

i573 : 
o573 = | wxz    wxy     0       |
       | wyz    x2z     x2y+wxz |
       | y3+xz2 xyz+wz2 xy2+wyz |

               3       3
o573 : Matrix R  <--- R

i574 :                      
o574 = 0

i575 :        
i576 : 
o576 : Ideal of R

i577 : 
o577 : Ideal of R

i578 : 
i579 : 
i580 : 
i581 : 
i582 : 
               3       3
o582 : Matrix R  <--- R

i583 : 
i584 :        
i585 : 
i586 : 
i587 : 
i588 : (0, 0)

i589 :               i=1;
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    print(prune subquotient (gens B, gens C));





i590 : 
i591 : 
o591 : Ideal of R

i592 : 
o592 : Ideal of R

i593 : 
i594 : 
i595 : 
i596 : 
i597 : 
               3       3
o597 : Matrix R  <--- R

i598 : 
i599 : 0

i600 :                             E3=generatingMorphism(I,3)
A=matrix entries relations E3#0
T=target A
U=matrix entries E3#1


------------------------------------
i=0

    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    -- im B = im C!
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
assert (X!=0);
     	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
    print(answer, prune subquotient (gens B, gens C));
    


o600 = (cokernel {-5} | z y x w |, 0)

o600 : Sequence

i601 : 
o601 = | z y x w |

               1       4
o601 : Matrix R  <--- R

i602 : 
        1
o602 = R

o602 : R-module, free

i603 : 
o603 = 0

               1       1
o603 : Matrix R  <--- R

i604 :                      
o604 = 0

i605 :        
i606 : 
o606 : Ideal of R

i607 : 
o607 : Ideal of R

i608 : 
i609 : 
i610 : 
i611 : 
i612 : 
               1       1
o612 : Matrix R  <--- R

i613 : 
i614 :        
i615 : 
i616 : 
i617 : 
i618 : (0, cokernel | z y x w |)

i619 :               
i=1;
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    print(prune subquotient (gens B, gens C));

       
i620 : 
i621 : 
o621 : Ideal of R

i622 : 
o622 : Ideal of R

i623 : 
i624 : 
i625 : 
i626 : 
i627 : 
               1       1
o627 : Matrix R  <--- R

i628 : 
i629 : cokernel | z y x w |

i630 :        E3=generatingMorphism(I,3)
A=matrix entries relations E3#0
T=target A
U=matrix entries E3#1


------------------------------------
i=0

    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    -- im B = im C!
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
assert (X!=0);
     	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
    print(answer, prune subquotient (gens B, gens C));
    




i=1;
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
    assert (X!=0);
     	    G1:=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
    print(answer, prune subquotient (gens B, gens C));



o630 = (cokernel {-5} | z y x w |, 0)

o630 : Sequence

i631 : 
o631 = | z y x w |

               1       4
o631 : Matrix R  <--- R

i632 : 
        1
o632 = R

o632 : R-module, free

i633 : 
o633 = 0

               1       1
o633 : Matrix R  <--- R

i634 :                      
o634 = 0

i635 :        
i636 : 
o636 : Ideal of R

i637 : 
o637 : Ideal of R

i638 : 
i639 : 
i640 : 
i641 : 
i642 : 
               1       1
o642 : Matrix R  <--- R

i643 : 
i644 :        
i645 : 
i646 : 
i647 : 
i648 : (0, cokernel | z y x w |)

i649 :                                    
i650 : 
i651 : 
o651 : Ideal of R

i652 : 
o652 : Ideal of R

i653 : 
i654 : 
i655 : 
i656 : 
i657 : 
               1       1
o657 : Matrix R  <--- R

i658 : 
i659 : 
i660 : 
i661 : stdio:1329:13:(3): warning: local declaration of G1 shields variable with same name

i662 : 
i663 : (0, cokernel | z y x w |)

i664 :               E2=generatingMorphism(I,2)
A=matrix entries relations E2#0
T=target A
U=matrix entries E2#1


------------------------------------
i=0

    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    -- im B = im C!
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
assert (X!=0);
     	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
    print(answer, prune subquotient (gens B, gens C));
    




i=1;
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
    assert (X!=0);
     	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
    print(answer, prune subquotient (gens B, gens C));








o664 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o664 : Sequence

i665 : 
o665 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o665 : Matrix R  <--- R

i666 : 
        3
o666 = R

o666 : R-module, free

i667 : 
o667 = | wxz    wxy     0       |
       | wyz    x2z     x2y+wxz |
       | y3+xz2 xyz+wz2 xy2+wyz |

               3       3
o667 : Matrix R  <--- R

i668 :                      
o668 = 0

i669 :        
i670 : 
o670 : Ideal of R

i671 : 
o671 : Ideal of R

i672 : 
i673 : 
i674 : 
i675 : 
i676 : 
               3       3
o676 : Matrix R  <--- R

i677 : 
i678 :        
i679 : 
i680 : 
i681 : 
i682 : (0, 0)

i683 :                                    
i684 : 
i685 : 
o685 : Ideal of R

i686 : 
o686 : Ideal of R

i687 : 
i688 : 
i689 : 
i690 : 
i691 : 
               3       3
o691 : Matrix R  <--- R

i692 : 
i693 : 
i694 : 
i695 : 
i696 : 
i697 : (0, 0)

i698 :                                                  
E3=generatingMorphism(I,3)
A=matrix entries relations E3#0
T=target A
U=matrix entries E3#1


       
o698 = (cokernel {-5} | z y x w |, 0)

o698 : Sequence

i699 : 
o699 = | z y x w |

               1       4
o699 : Matrix R  <--- R

i700 : 
        1
o700 = R

o700 : R-module, free

i701 : 
o701 = 0

               1       1
o701 : Matrix R  <--- R

i702 :    T              T           

        1
o702 = R

o702 : R-module, free

i703 : U

o703 = 0

               1       1
o703 : Matrix R  <--- R

i704 : dim R

o704 = 4

i705 : E2=generatingMorphism(I,2)


o705 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o705 : Sequence

i706 :        E3=generatingMorphism(I,3)


o706 = (cokernel {-5} | z y x w |, 0)

o706 : Sequence

i707 :        E0=generatingMorphism(I,0)
E1=generatingMorphism(I,1)
E2=generatingMorphism(I,2)
E3=generatingMorphism(I,3)
E4=generatingMorphism(I,4)



o707 = (image 0, 0)

o707 : Sequence

i708 : 
o708 = (0, 0)

o708 : Sequence

i709 : 
o709 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o709 : Sequence

i710 : 
o710 = (cokernel {-5} | z y x w |, 0)

o710 : Sequence

i711 : 
o711 = (0, 0)

o711 : Sequence

i712 :               E0=generatingMorphism(I,0)


o712 = (image 0, 0)

o712 : Sequence

i713 :        E0=generatingMorphism(I,0)
E1=generatingMorphism(I,1)


o713 = (image 0, 0)

o713 : Sequence

i714 : 
o714 = (0, 0)

o714 : Sequence

i715 :        E0=generatingMorphism(I,0)
E1=generatingMorphism(I,1)
E2=generatingMorphism(I,2)


o715 = (image 0, 0)

o715 : Sequence

i716 : 
o716 = (0, 0)

o716 : Sequence

i717 : 
o717 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o717 : Sequence

i718 :        E0=generatingMorphism(I,0)
E1=generatingMorphism(I,1)
E2=generatingMorphism(I,2)
E3=generatingMorphism(I,3)


o718 = (image 0, 0)

o718 : Sequence

i719 : 
o719 = (0, 0)

o719 : Sequence

i720 : 
o720 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o720 : Sequence

i721 : 
o721 = (cokernel {-5} | z y x w |, 0)

o721 : Sequence

i722 :        E0=generatingMorphism(I,0)
E1=generatingMorphism(I,1)
E2=generatingMorphism(I,2)
E3=generatingMorphism(I,3)
E4=generatingMorphism(I,4)


o722 = (image 0, 0)

o722 : Sequence

i723 : 
o723 = (0, 0)

o723 : Sequence

i724 : 
o724 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o724 : Sequence

i725 : 
o725 = (cokernel {-5} | z y x w |, 0)

o725 : Sequence

i726 : 
o726 = (0, 0)

o726 : Sequence

i727 :        p=2;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;
time LT=LyubeznikTable(I)
peek(LT)


i728 : 
i729 :        
o729 : Ideal of R

i730 : 
               1       4
o730 : Matrix R  <--- R

i731 :      -- used 0.225685 seconds

o731 = MutableHashTable{...1...}

o731 : MutableHashTable

i732 : 
o732 = MutableHashTable{(2, 2) => 1}

i733 :        E2=generatingMorphism(I,2)
A=matrix entries relations E3#0
T=target A
U=matrix entries E3#1


------------------------------------
i=0

    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    -- im B = im C!
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
assert (X!=0);
     	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
    print(answer, prune subquotient (gens B, gens C));
    




i=1;
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
    assert (X!=0);
     	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
    print(answer, prune subquotient (gens B, gens C));



i=2;
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
    assert (X!=0);
     	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
    print(answer, prune subquotient (gens B, gens C));











o733 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o733 : Sequence

i734 : 
o734 = | z y x w |

               ZZ       1       ZZ       4
o734 : Matrix (--[w..z])  <--- (--[w..z])
                2                2

i735 : 
        ZZ       1
o735 = (--[w..z])
         2

       ZZ
o735 : --[w..z]-module, free
        2

i736 : 
o736 = 0

               ZZ       1       ZZ       1
o736 : Matrix (--[w..z])  <--- (--[w..z])
                2                2

i737 :                      
o737 = 0

i738 :        stdio:108:12:(3):[1]: error: expected ideal and module for the same ring

i739 : 
o739 : Ideal of R

i740 : 
o740 : Ideal of R

i741 : 
i742 : 
i743 : 
i744 : stdio:1449:10:(3): error: expected ideal and module for the same ring

i745 : stdio:1450:8:(3): error: no method found for applying promote to:
     argument 1 :  1 (of class R)
                   ZZ
     argument 2 :  --[w..z]
                    2

i746 : stdio:1451:9:(3): error: expected ideal and module for the same ring

i747 :        
i748 : 
i749 : stdio:1455:16:(3): error: expected compatible rings

i750 : 
i751 : (0, 0)

i752 :                                    
i753 : stdio:108:12:(3):[1]: error: expected ideal and module for the same ring

i754 : 
                ZZ
o754 : Ideal of --[w..z]
                 2

i755 : 
                ZZ
o755 : Ideal of --[w..z]
                 2

i756 : 
i757 : 
i758 : 
i759 : 
i760 : 
               ZZ       1       ZZ       1
o760 : Matrix (--[w..z])  <--- (--[w..z])
                2                2

i761 : 
i762 : 
i763 : 
i764 : stdio:1475:16:(3): error: expected compatible rings

i765 : 
i766 : (0, cokernel | z y x w |)

i767 :                      
i768 : stdio:108:12:(3):[1]: error: expected ideal and module for the same ring

i769 : 
                ZZ
o769 : Ideal of --[w..z]
                 2

i770 :  *** FATAL ERROR *** lowLimClosure, sequence too short

i771 : 
i772 : stdio:1486:8:(3): error: array index 2 out of bounds 0 .. 1

i773 : 
i774 : stdio:1488:10:(3): error: no method for binary operator * applied to objects:
--            null (of class Nothing)
--             ZZ       1
--      *     (--[w..z])  (of class Module)
--              2

i775 : 
               ZZ       1       ZZ       1
o775 : Matrix (--[w..z])  <--- (--[w..z])
                2                2

i776 : 
i777 : 
i778 : 
i779 : stdio:1493:16:(3): error: expected compatible rings

i780 : 
i781 : (0, cokernel | z y x w |)

i782 :                                                                       E2=generatingMorphism(I,2)
A=matrix entries relations E2#0
T=target A
U=matrix entries E2#1



o782 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o782 : Sequence

i783 : 
o783 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o783 : Matrix R  <--- R

i784 : 
        3
o784 = R

o784 : R-module, free

i785 : 
o785 = | wxz    wxy     0       |
       | wyz    x2z     x2y+wxz |
       | y3+xz2 xyz+wz2 xy2+wyz |

               3       3
o785 : Matrix R  <--- R

i786 :               E2=generatingMorphism(I,2)
A=matrix entries relations E2#0
T=target A
U=matrix entries E2#1


------------------------------------
i=0

    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    -- im B = im C!
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
assert (X!=0);
     	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
    print(answer, prune subquotient (gens B, gens C));
    


o786 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o786 : Sequence

i787 : 
o787 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o787 : Matrix R  <--- R

i788 : 
        3
o788 = R

o788 : R-module, free

i789 : 
o789 = | wxz    wxy     0       |
       | wyz    x2z     x2y+wxz |
       | y3+xz2 xyz+wz2 xy2+wyz |

               3       3
o789 : Matrix R  <--- R

i790 :                      
o790 = 0

i791 :        
i792 : 
o792 : Ideal of R

i793 : 
o793 : Ideal of R

i794 : 
i795 : 
i796 : 
i797 : 
i798 : 
               3       3
o798 : Matrix R  <--- R

i799 : 
i800 :        
i801 : 
i802 : 
i803 : 
i804 : (0, 0)

i805 :               E2=generatingMorphism(I,2)
A=matrix entries relations E2#0
T=target A
U=matrix entries E2#1


------------------------------------
i=0

    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    -- im B = im C!
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
assert (X!=0);
     	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
    print(answer, prune subquotient (gens B, gens C));
    




i=1;
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
    assert (X!=0);
     	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
    print(answer, prune subquotient (gens B, gens C));



o805 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o805 : Sequence

i806 : 
o806 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o806 : Matrix R  <--- R

i807 : 
        3
o807 = R

o807 : R-module, free

i808 : 
o808 = | wxz    wxy     0       |
       | wyz    x2z     x2y+wxz |
       | y3+xz2 xyz+wz2 xy2+wyz |

               3       3
o808 : Matrix R  <--- R

i809 :                      
o809 = 0

i810 :        
i811 : 
o811 : Ideal of R

i812 : 
o812 : Ideal of R

i813 : 
i814 : 
i815 : 
i816 : 
i817 : 
               3       3
o817 : Matrix R  <--- R

i818 : 
i819 :        
i820 : 
i821 : 
i822 : 
i823 : (0, 0)

i824 :                                    
i825 : 
i826 : 
o826 : Ideal of R

i827 : 
o827 : Ideal of R

i828 : 
i829 : 
i830 : 
i831 : 
i832 : 
               3       3
o832 : Matrix R  <--- R

i833 : 
i834 : 
i835 : 
i836 : 
i837 : 
i838 : (0, 0)

i839 :               

i=2;
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
    assert (X!=0);
     	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
    print(answer, prune subquotient (gens B, gens C));


              
i840 : 
i841 : 
o841 : Ideal of R

i842 : 
o842 : Ideal of R

i843 : 
i844 : 
i845 : 
i846 : 
i847 : 
               3       3
o847 : Matrix R  <--- R

i848 : 
i849 : 
i850 : 
i851 : 
i852 : 
i853 : (1, cokernel | z y w 0 0 0 0 0 x 0 0 |)
             | 0 0 0 z y x w 0 0 0 0 |
             | 0 0 0 0 0 0 0 z y x w |

i854 :      I              I         

o854 = | xy+wz y3+xz2 wy2+x2z x3+w2y |

               1       4
o854 : Matrix R  <--- R

i855 : res coker I

        1      4      4      1
o855 = R  <-- R  <-- R  <-- R  <-- 0
                                    
       0      1      2      3      4

o855 : ChainComplex

i856 : www=res coker I

        1      4      4      1
o856 = R  <-- R  <-- R  <-- R  <-- 0
                                    
       0      1      2      3      4

o856 : ChainComplex

i857 : c.dd
stdio:1606:2:(3): error: expected argument 1 to be a hash table

i858 : peek www

o858 = ChainComplex{4 => 0                                                  }
                    cache => CacheTable{}
                    complete => true
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy+wz x3+w2y wy2+x2z y3+xz2 |

                               4                           4
                          1 : R  <----------------------- R  : 2
                                    {2} | x2 wy xz y2 |
                                    {3} | y  z  0  0  |
                                    {3} | w  x  y  z  |
                                    {3} | 0  0  w  x  |

                               4                 1
                          2 : R  <------------- R  : 3
                                    {4} | z |
                                    {4} | y |
                                    {4} | x |
                                    {4} | w |

                               1
                          3 : R  <----- 0 : 4
                                    0
                          1
                    0 => R
                          1
                    3 => R
                          4
                    1 => R
                          4
                    2 => R

i859 : p=2;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;
www=res coker I;


i860 : 
i861 :        
o861 : Ideal of R

i862 : 
               1       4
o862 : Matrix R  <--- R

i863 : 
i864 :        p=2;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;
www=res coker I;
peek(www);


i865 : 
i866 :        
o866 : Ideal of R

i867 : 
               1       4
o867 : Matrix R  <--- R

i868 : 
i869 : 
i870 :        peek(www)


o870 = ChainComplex{4 => 0                                                  }
                    cache => CacheTable{}
                    complete => true
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy+wz x3+w2y wy2+x2z y3+xz2 |

                               4                           4
                          1 : R  <----------------------- R  : 2
                                    {2} | x2 wy xz y2 |
                                    {3} | y  z  0  0  |
                                    {3} | w  x  y  z  |
                                    {3} | 0  0  w  x  |

                               4                 1
                          2 : R  <------------- R  : 3
                                    {4} | z |
                                    {4} | y |
                                    {4} | x |
                                    {4} | w |

                               1
                          3 : R  <----- 0 : 4
                                    0
                          1
                    0 => R
                          1
                    3 => R
                          4
                    1 => R
                          4
                    2 => R

i871 :        R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;
www=res coker I;
peek(www)


i872 : 
o872 : Ideal of R

i873 : 
               1       4
o873 : Matrix R  <--- R

i874 : 
i875 : 
o875 = ChainComplex{cache => CacheTable{}                                                                                                                                               }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy+wz x3+w2y wy2+x2z y3+xz2 |

                               4                                                                                                                                                   9
                          1 : R  <----------------------------------------------------------------------------------------------------------------------------------------------- R  : 2
                                    {2} | 1/2x3+1/2w2y 1/2x2y-1/2wxz 0            -1/2wy2-1/2x2z -1/2xy2+1/2wyz -1/2y3-1/2xz2 -1/2wx2y+1/2w2xz 0             -1/2xy2z+1/2wyz2 |
                                    {3} | -1/2xy-1/2wz -1/2y2        1/2yz        0              -1/2z2         0             -1/2x2z          1/2xz2        -1/2z3           |
                                    {3} | 0            0             -1/2xy-1/2wz 1/2xy+1/2wz    0              0             1/2x3+1/2w2y     1/2wy2-1/2x2z 1/2y3+1/2xz2     |
                                    {3} | 0            1/2w2         1/2wx        0              1/2x2          1/2xy+1/2wz   -1/2w3           -1/2w2y       -1/2wy2          |

                               9                                         8
                          2 : R  <------------------------------------- R  : 3
                                    {5} | -y -z 0  0  xz 0   -z2 0  |
                                    {5} | x  0  -z 0  0  -wz 0   yz |
                                    {5} | -w -x -y -z 0  -wy 0   y2 |
                                    {5} | -w -x -y -z x2 0   -xz 0  |
                                    {5} | 0  w  0  -y 0  0   0   0  |
                                    {5} | 0  0  w  x  0  0   0   0  |
                                    {6} | 0  0  0  0  -y -z  0   0  |
                                    {6} | 0  0  0  0  w  -x  -y  z  |
                                    {6} | 0  0  0  0  0  0   w   x  |

                               8                     2
                          3 : R  <----------------- R  : 4
                                    {6} | -z 0  |
                                    {6} | y  0  |
                                    {6} | -x 0  |
                                    {6} | w  0  |
                                    {7} | 0  -z |
                                    {7} | 0  y  |
                                    {7} | 0  -x |
                                    {7} | 0  w  |

                               2
                          4 : R  <----- 0 : 5
                                    0

i876 :        p=101;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;
www=res coker I;
peek(www)


i877 : 
i878 :        
o878 : Ideal of R

i879 : 
               1       4
o879 : Matrix R  <--- R

i880 : 
i881 : 
o881 = ChainComplex{cache => CacheTable{}                                                                                                                          }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy+wz x3+w2y wy2+x2z y3+xz2 |

                               4                                                                                                                              9
                          1 : R  <-------------------------------------------------------------------------------------------------------------------------- R  : 2
                                    {2} | -50x3-50w2y -50x2y+50wxz 0         50wy2+50x2z 50xy2-50wyz 50y3+50xz2 50wx2y-50w2xz 0            50xy2z-50wyz2 |
                                    {3} | 50xy+50wz   50y2         -50yz     0           50z2        0          50x2z         -50xz2       50z3          |
                                    {3} | 0           0            50xy+50wz -50xy-50wz  0           0          -50x3-50w2y   -50wy2+50x2z -50y3-50xz2   |
                                    {3} | 0           -50w2        -50wx     0           -50x2       -50xy-50wz 50w3          50w2y        50wy2         |

                               9                                         8
                          2 : R  <------------------------------------- R  : 3
                                    {5} | -y -z 0  0  xz 0   -z2 0  |
                                    {5} | x  0  -z 0  0  -wz 0   yz |
                                    {5} | -w -x -y -z 0  -wy 0   y2 |
                                    {5} | -w -x -y -z x2 0   -xz 0  |
                                    {5} | 0  w  0  -y 0  0   0   0  |
                                    {5} | 0  0  w  x  0  0   0   0  |
                                    {6} | 0  0  0  0  -y -z  0   0  |
                                    {6} | 0  0  0  0  w  -x  -y  z  |
                                    {6} | 0  0  0  0  0  0   w   x  |

                               8                     2
                          3 : R  <----------------- R  : 4
                                    {6} | -z 0  |
                                    {6} | y  0  |
                                    {6} | -x 0  |
                                    {6} | w  0  |
                                    {7} | 0  -z |
                                    {7} | 0  y  |
                                    {7} | 0  -x |
                                    {7} | 0  w  |

                               2
                          4 : R  <----- 0 : 5
                                    0

i882 :        p=3;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;
www=res coker I;
peek(www)


i883 : 
i884 :        
o884 : Ideal of R

i885 : 
               1       4
o885 : Matrix R  <--- R

i886 : 
i887 : 
o887 = ChainComplex{cache => CacheTable{}                                                                                      }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy+wz x3+w2y wy2+x2z y3+xz2 |

                               4                                                                                          9
                          1 : R  <-------------------------------------------------------------------------------------- R  : 2
                                    {2} | -x3-w2y -x2y+wxz 0     wy2+x2z xy2-wyz y3+xz2 wx2y-w2xz 0        xy2z-wyz2 |
                                    {3} | xy+wz   y2       -yz   0       z2      0      x2z       -xz2     z3        |
                                    {3} | 0       0        xy+wz -xy-wz  0       0      -x3-w2y   -wy2+x2z -y3-xz2   |
                                    {3} | 0       -w2      -wx   0       -x2     -xy-wz w3        w2y      wy2       |

                               9                                         8
                          2 : R  <------------------------------------- R  : 3
                                    {5} | -y -z 0  0  xz 0   -z2 0  |
                                    {5} | x  0  -z 0  0  -wz 0   yz |
                                    {5} | -w -x -y -z 0  -wy 0   y2 |
                                    {5} | -w -x -y -z x2 0   -xz 0  |
                                    {5} | 0  w  0  -y 0  0   0   0  |
                                    {5} | 0  0  w  x  0  0   0   0  |
                                    {6} | 0  0  0  0  -y -z  0   0  |
                                    {6} | 0  0  0  0  w  -x  -y  z  |
                                    {6} | 0  0  0  0  0  0   w   x  |

                               8                     2
                          3 : R  <----------------- R  : 4
                                    {6} | -z 0  |
                                    {6} | y  0  |
                                    {6} | -x 0  |
                                    {6} | w  0  |
                                    {7} | 0  -z |
                                    {7} | 0  y  |
                                    {7} | 0  -x |
                                    {7} | 0  w  |

                               2
                          4 : R  <----- 0 : 5
                                    0

i888 :        p=5;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;
www=res coker I;
peek(www)


i889 : 
i890 :        
o890 : Ideal of R

i891 : 
               1       4
o891 : Matrix R  <--- R

i892 : 
i893 : 
o893 = ChainComplex{cache => CacheTable{}                                                                                                        }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy+wz x3+w2y wy2+x2z y3+xz2 |

                               4                                                                                                            9
                          1 : R  <-------------------------------------------------------------------------------------------------------- R  : 2
                                    {2} | -2x3-2w2y -2x2y+2wxz 0       2wy2+2x2z 2xy2-2wyz 2y3+2xz2 2wx2y-2w2xz 0          2xy2z-2wyz2 |
                                    {3} | 2xy+2wz   2y2        -2yz    0         2z2       0        2x2z        -2xz2      2z3         |
                                    {3} | 0         0          2xy+2wz -2xy-2wz  0         0        -2x3-2w2y   -2wy2+2x2z -2y3-2xz2   |
                                    {3} | 0         -2w2       -2wx    0         -2x2      -2xy-2wz 2w3         2w2y       2wy2        |

                               9                                         8
                          2 : R  <------------------------------------- R  : 3
                                    {5} | -y -z 0  0  xz 0   -z2 0  |
                                    {5} | x  0  -z 0  0  -wz 0   yz |
                                    {5} | -w -x -y -z 0  -wy 0   y2 |
                                    {5} | -w -x -y -z x2 0   -xz 0  |
                                    {5} | 0  w  0  -y 0  0   0   0  |
                                    {5} | 0  0  w  x  0  0   0   0  |
                                    {6} | 0  0  0  0  -y -z  0   0  |
                                    {6} | 0  0  0  0  w  -x  -y  z  |
                                    {6} | 0  0  0  0  0  0   w   x  |

                               8                     2
                          3 : R  <----------------- R  : 4
                                    {6} | -z 0  |
                                    {6} | y  0  |
                                    {6} | -x 0  |
                                    {6} | w  0  |
                                    {7} | 0  -z |
                                    {7} | 0  y  |
                                    {7} | 0  -x |
                                    {7} | 0  w  |

                               2
                          4 : R  <----- 0 : 5
                                    0

i894 :        p=2;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;
www=res coker I;
peek(www)


i895 : 
i896 :        
o896 : Ideal of R

i897 : 
               1       4
o897 : Matrix R  <--- R

i898 : 
i899 : 
o899 = ChainComplex{cache => CacheTable{}                                   }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy+wz x3+w2y wy2+x2z y3+xz2 |

                               4                           4
                          1 : R  <----------------------- R  : 2
                                    {2} | x2 wy xz y2 |
                                    {3} | y  z  0  0  |
                                    {3} | w  x  y  z  |
                                    {3} | 0  0  w  x  |

                               4                 1
                          2 : R  <------------- R  : 3
                                    {4} | z |
                                    {4} | y |
                                    {4} | x |
                                    {4} | w |

                               1
                          3 : R  <----- 0 : 4
                                    0

i900 :        p=3;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;
www=res coker I;
peek(www)


i901 : 
i902 :        
o902 : Ideal of R

i903 : 
               1       4
o903 : Matrix R  <--- R

i904 : 
i905 : 
o905 = ChainComplex{cache => CacheTable{}                                                                                      }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy+wz x3+w2y wy2+x2z y3+xz2 |

                               4                                                                                          9
                          1 : R  <-------------------------------------------------------------------------------------- R  : 2
                                    {2} | -x3-w2y -x2y+wxz 0     wy2+x2z xy2-wyz y3+xz2 wx2y-w2xz 0        xy2z-wyz2 |
                                    {3} | xy+wz   y2       -yz   0       z2      0      x2z       -xz2     z3        |
                                    {3} | 0       0        xy+wz -xy-wz  0       0      -x3-w2y   -wy2+x2z -y3-xz2   |
                                    {3} | 0       -w2      -wx   0       -x2     -xy-wz w3        w2y      wy2       |

                               9                                         8
                          2 : R  <------------------------------------- R  : 3
                                    {5} | -y -z 0  0  xz 0   -z2 0  |
                                    {5} | x  0  -z 0  0  -wz 0   yz |
                                    {5} | -w -x -y -z 0  -wy 0   y2 |
                                    {5} | -w -x -y -z x2 0   -xz 0  |
                                    {5} | 0  w  0  -y 0  0   0   0  |
                                    {5} | 0  0  w  x  0  0   0   0  |
                                    {6} | 0  0  0  0  -y -z  0   0  |
                                    {6} | 0  0  0  0  w  -x  -y  z  |
                                    {6} | 0  0  0  0  0  0   w   x  |

                               8                     2
                          3 : R  <----------------- R  : 4
                                    {6} | -z 0  |
                                    {6} | y  0  |
                                    {6} | -x 0  |
                                    {6} | w  0  |
                                    {7} | 0  -z |
                                    {7} | 0  y  |
                                    {7} | 0  -x |
                                    {7} | 0  w  |

                               2
                          4 : R  <----- 0 : 5
                                    0

i906 :        p=3;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


i907 : 
i908 :        
o908 : Ideal of R

i909 : 
               1       4
o909 : Matrix R  <--- R

i910 : 
i911 : 
o911 = ChainComplex{cache => CacheTable{}                                                                                      }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy+wz x3+w2y wy2+x2z y3+xz2 |

                               4                                                                                          9
                          1 : R  <-------------------------------------------------------------------------------------- R  : 2
                                    {2} | -x3-w2y -x2y+wxz 0     wy2+x2z xy2-wyz y3+xz2 wx2y-w2xz 0        xy2z-wyz2 |
                                    {3} | xy+wz   y2       -yz   0       z2      0      x2z       -xz2     z3        |
                                    {3} | 0       0        xy+wz -xy-wz  0       0      -x3-w2y   -wy2+x2z -y3-xz2   |
                                    {3} | 0       -w2      -wx   0       -x2     -xy-wz w3        w2y      wy2       |

                               9                                         8
                          2 : R  <------------------------------------- R  : 3
                                    {5} | -y -z 0  0  xz 0   -z2 0  |
                                    {5} | x  0  -z 0  0  -wz 0   yz |
                                    {5} | -w -x -y -z 0  -wy 0   y2 |
                                    {5} | -w -x -y -z x2 0   -xz 0  |
                                    {5} | 0  w  0  -y 0  0   0   0  |
                                    {5} | 0  0  w  x  0  0   0   0  |
                                    {6} | 0  0  0  0  -y -z  0   0  |
                                    {6} | 0  0  0  0  w  -x  -y  z  |
                                    {6} | 0  0  0  0  0  0   w   x  |

                               8                     2
                          3 : R  <----------------- R  : 4
                                    {6} | -z 0  |
                                    {6} | y  0  |
                                    {6} | -x 0  |
                                    {6} | w  0  |
                                    {7} | 0  -z |
                                    {7} | 0  y  |
                                    {7} | 0  -x |
                                    {7} | 0  w  |

                               2
                          4 : R  <----- 0 : 5
                                    0

i912 :      -- used 0.483334 seconds

o912 = MutableHashTable{...1...}

o912 : MutableHashTable

i913 : 
o913 = MutableHashTable{(1, 1) => 1}

i914 :        p=2;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


i915 : 
i916 :        
o916 : Ideal of R

i917 : 
               1       4
o917 : Matrix R  <--- R

i918 : 
i919 : 
o919 = ChainComplex{cache => CacheTable{}                                   }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy+wz x3+w2y wy2+x2z y3+xz2 |

                               4                           4
                          1 : R  <----------------------- R  : 2
                                    {2} | x2 wy xz y2 |
                                    {3} | y  z  0  0  |
                                    {3} | w  x  y  z  |
                                    {3} | 0  0  w  x  |

                               4                 1
                          2 : R  <------------- R  : 3
                                    {4} | z |
                                    {4} | y |
                                    {4} | x |
                                    {4} | w |

                               1
                          3 : R  <----- 0 : 4
                                    0

i920 :      -- used 0.258153 seconds

o920 = MutableHashTable{...1...}

o920 : MutableHashTable

i921 : 
o921 = MutableHashTable{(2, 2) => 1}

i922 :        p=2;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


i923 : 
i924 :        
o924 : Ideal of R

i925 : 
               1       4
o925 : Matrix R  <--- R

i926 : 
i927 : 
o927 = ChainComplex{cache => CacheTable{}                                   }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy+wz x3+w2y wy2+x2z y3+xz2 |

                               4                           4
                          1 : R  <----------------------- R  : 2
                                    {2} | x2 wy xz y2 |
                                    {3} | y  z  0  0  |
                                    {3} | w  x  y  z  |
                                    {3} | 0  0  w  x  |

                               4                 1
                          2 : R  <------------- R  : 3
                                    {4} | z |
                                    {4} | y |
                                    {4} | x |
                                    {4} | w |

                               1
                          3 : R  <----- 0 : 4
                                    0

i928 :      -- used 0.244422 seconds

o928 = MutableHashTable{...1...}

o928 : MutableHashTable

i929 : 
o929 = MutableHashTable{(2, 2) => 1}

i930 :        p=3;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


i931 : 
i932 :        
o932 : Ideal of R

i933 : 
               1       4
o933 : Matrix R  <--- R

i934 : 
i935 : 
o935 = ChainComplex{cache => CacheTable{}                                                                                      }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy+wz x3+w2y wy2+x2z y3+xz2 |

                               4                                                                                          9
                          1 : R  <-------------------------------------------------------------------------------------- R  : 2
                                    {2} | -x3-w2y -x2y+wxz 0     wy2+x2z xy2-wyz y3+xz2 wx2y-w2xz 0        xy2z-wyz2 |
                                    {3} | xy+wz   y2       -yz   0       z2      0      x2z       -xz2     z3        |
                                    {3} | 0       0        xy+wz -xy-wz  0       0      -x3-w2y   -wy2+x2z -y3-xz2   |
                                    {3} | 0       -w2      -wx   0       -x2     -xy-wz w3        w2y      wy2       |

                               9                                         8
                          2 : R  <------------------------------------- R  : 3
                                    {5} | -y -z 0  0  xz 0   -z2 0  |
                                    {5} | x  0  -z 0  0  -wz 0   yz |
                                    {5} | -w -x -y -z 0  -wy 0   y2 |
                                    {5} | -w -x -y -z x2 0   -xz 0  |
                                    {5} | 0  w  0  -y 0  0   0   0  |
                                    {5} | 0  0  w  x  0  0   0   0  |
                                    {6} | 0  0  0  0  -y -z  0   0  |
                                    {6} | 0  0  0  0  w  -x  -y  z  |
                                    {6} | 0  0  0  0  0  0   w   x  |

                               8                     2
                          3 : R  <----------------- R  : 4
                                    {6} | -z 0  |
                                    {6} | y  0  |
                                    {6} | -x 0  |
                                    {6} | w  0  |
                                    {7} | 0  -z |
                                    {7} | 0  y  |
                                    {7} | 0  -x |
                                    {7} | 0  w  |

                               2
                          4 : R  <----- 0 : 5
                                    0

i936 :      -- used 0.457124 seconds

o936 = MutableHashTable{...1...}

o936 : MutableHashTable

i937 : 
o937 = MutableHashTable{(1, 1) => 1}

i938 :        p=5;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)



i939 : 
i940 :        
o940 : Ideal of R

i941 : 
               1       4
o941 : Matrix R  <--- R

i942 : 
i943 : 
o943 = ChainComplex{cache => CacheTable{}                                                                                                        }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy+wz x3+w2y wy2+x2z y3+xz2 |

                               4                                                                                                            9
                          1 : R  <-------------------------------------------------------------------------------------------------------- R  : 2
                                    {2} | -2x3-2w2y -2x2y+2wxz 0       2wy2+2x2z 2xy2-2wyz 2y3+2xz2 2wx2y-2w2xz 0          2xy2z-2wyz2 |
                                    {3} | 2xy+2wz   2y2        -2yz    0         2z2       0        2x2z        -2xz2      2z3         |
                                    {3} | 0         0          2xy+2wz -2xy-2wz  0         0        -2x3-2w2y   -2wy2+2x2z -2y3-2xz2   |
                                    {3} | 0         -2w2       -2wx    0         -2x2      -2xy-2wz 2w3         2w2y       2wy2        |

                               9                                         8
                          2 : R  <------------------------------------- R  : 3
                                    {5} | -y -z 0  0  xz 0   -z2 0  |
                                    {5} | x  0  -z 0  0  -wz 0   yz |
                                    {5} | -w -x -y -z 0  -wy 0   y2 |
                                    {5} | -w -x -y -z x2 0   -xz 0  |
                                    {5} | 0  w  0  -y 0  0   0   0  |
                                    {5} | 0  0  w  x  0  0   0   0  |
                                    {6} | 0  0  0  0  -y -z  0   0  |
                                    {6} | 0  0  0  0  w  -x  -y  z  |
                                    {6} | 0  0  0  0  0  0   w   x  |

                               8                     2
                          3 : R  <----------------- R  : 4
                                    {6} | -z 0  |
                                    {6} | y  0  |
                                    {6} | -x 0  |
                                    {6} | w  0  |
                                    {7} | 0  -z |
                                    {7} | 0  y  |
                                    {7} | 0  -x |
                                    {7} | 0  w  |

                               2
                          4 : R  <----- 0 : 5
                                    0

i944 :      -- used 0.496056 seconds

o944 = MutableHashTable{...1...}

o944 : MutableHashTable

i945 : 
o945 = MutableHashTable{(1, 1) => 1}

i946 :               p=7;
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)



i947 : 
i948 :        
o948 : Ideal of R

i949 : 
               1       4
o949 : Matrix R  <--- R

i950 : 
i951 : 
o951 = ChainComplex{cache => CacheTable{}                                                                                                        }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy+wz x3+w2y wy2+x2z y3+xz2 |

                               4                                                                                                            9
                          1 : R  <-------------------------------------------------------------------------------------------------------- R  : 2
                                    {2} | -3x3-3w2y -3x2y+3wxz 0       3wy2+3x2z 3xy2-3wyz 3y3+3xz2 3wx2y-3w2xz 0          3xy2z-3wyz2 |
                                    {3} | 3xy+3wz   3y2        -3yz    0         3z2       0        3x2z        -3xz2      3z3         |
                                    {3} | 0         0          3xy+3wz -3xy-3wz  0         0        -3x3-3w2y   -3wy2+3x2z -3y3-3xz2   |
                                    {3} | 0         -3w2       -3wx    0         -3x2      -3xy-3wz 3w3         3w2y       3wy2        |

                               9                                         8
                          2 : R  <------------------------------------- R  : 3
                                    {5} | -y -z 0  0  xz 0   -z2 0  |
                                    {5} | x  0  -z 0  0  -wz 0   yz |
                                    {5} | -w -x -y -z 0  -wy 0   y2 |
                                    {5} | -w -x -y -z x2 0   -xz 0  |
                                    {5} | 0  w  0  -y 0  0   0   0  |
                                    {5} | 0  0  w  x  0  0   0   0  |
                                    {6} | 0  0  0  0  -y -z  0   0  |
                                    {6} | 0  0  0  0  w  -x  -y  z  |
                                    {6} | 0  0  0  0  0  0   w   x  |

                               8                     2
                          3 : R  <----------------- R  : 4
                                    {6} | -z 0  |
                                    {6} | y  0  |
                                    {6} | -x 0  |
                                    {6} | w  0  |
                                    {7} | 0  -z |
                                    {7} | 0  y  |
                                    {7} | 0  -x |
                                    {7} | 0  w  |

                               2
                          4 : R  <----- 0 : 5
                                    0

i952 :      -- used 0.658519 seconds

o952 = MutableHashTable{...1...}

o952 : MutableHashTable

i953 : 
o953 = MutableHashTable{(1, 1) => 1}

i954 :               p=2; --- p=2 behaves differently!
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y+w*z, y^3+x*z^2, w*y^2+x^2*z, x^3+w^2*y);
I=gens I;
www=res coker I;
peek(www)


i955 : 
i956 :        
o956 : Ideal of R

i957 : 
               1       4
o957 : Matrix R  <--- R

i958 : 
i959 : 
o959 = ChainComplex{cache => CacheTable{}                                   }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy+wz x3+w2y wy2+x2z y3+xz2 |

                               4                           4
                          1 : R  <----------------------- R  : 2
                                    {2} | x2 wy xz y2 |
                                    {3} | y  z  0  0  |
                                    {3} | w  x  y  z  |
                                    {3} | 0  0  w  x  |

                               4                 1
                          2 : R  <------------- R  : 3
                                    {4} | z |
                                    {4} | y |
                                    {4} | x |
                                    {4} | w |

                               1
                          3 : R  <----- 0 : 4
                                    0

i960 :       dim coker I       dim coker I 

o960 = 2

i961 : length www

o961 = 3

i962 : p=3; --- p=2 behaves differently!
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


i963 : 
i964 :        
o964 : Ideal of R

i965 : 
               1       4
o965 : Matrix R  <--- R

i966 : 
i967 : 
o967 = ChainComplex{cache => CacheTable{}                                   }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy-wz x3-w2y wy2-x2z y3-xz2 |

                               4                               4
                          1 : R  <--------------------------- R  : 2
                                    {2} | -x2 -wy -xz -y2 |
                                    {3} | y   z   0   0   |
                                    {3} | w   x   -y  -z  |
                                    {3} | 0   0   w   x   |

                               4                  1
                          2 : R  <-------------- R  : 3
                                    {4} | z  |
                                    {4} | -y |
                                    {4} | -x |
                                    {4} | w  |

                               1
                          3 : R  <----- 0 : 4
                                    0

i968 :      -- used 0.253859 seconds

o968 = MutableHashTable{...1...}

o968 : MutableHashTable

i969 : 
o969 = MutableHashTable{(2, 2) => 1}

i970 :        R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;
www=res coker I;
peek(www)


i971 : 
o971 : Ideal of R

i972 : 
               1       4
o972 : Matrix R  <--- R

i973 : 
i974 : 
o974 = ChainComplex{cache => CacheTable{}                                   }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy-wz x3-w2y wy2-x2z y3-xz2 |

                               4                               4
                          1 : R  <--------------------------- R  : 2
                                    {2} | -x2 -wy -xz -y2 |
                                    {3} | y   z   0   0   |
                                    {3} | w   x   -y  -z  |
                                    {3} | 0   0   w   x   |

                               4                  1
                          2 : R  <-------------- R  : 3
                                    {4} | z  |
                                    {4} | -y |
                                    {4} | -x |
                                    {4} | w  |

                               1
                          3 : R  <----- 0 : 4
                                    0

i975 :        p=5; --- p=2 behaves differently!
--R=ZZ/p[w,x,y,z];
R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


i976 :        
i977 : 
o977 : Ideal of R

i978 : 
               1       4
o978 : Matrix R  <--- R

i979 : 
i980 : 
o980 = ChainComplex{cache => CacheTable{}                                   }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy-wz x3-w2y wy2-x2z y3-xz2 |

                               4                               4
                          1 : R  <--------------------------- R  : 2
                                    {2} | -x2 -wy -xz -y2 |
                                    {3} | y   z   0   0   |
                                    {3} | w   x   -y  -z  |
                                    {3} | 0   0   w   x   |

                               4                  1
                          2 : R  <-------------- R  : 3
                                    {4} | z  |
                                    {4} | -y |
                                    {4} | -x |
                                    {4} | w  |

                               1
                          3 : R  <----- 0 : 4
                                    0

i981 : stdio:89:12:(3):[2]: error: inducedMap: expected matrix to induce a well-defined map
     -- used 0.00179168 seconds

i982 : 
o982 = MutableHashTable{(2, 2) => 1}

i983 :        p=5; --- p=2 behaves differently!
--R=ZZ/p[w,x,y,z];
R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;


i984 :        
i985 : 
o985 : Ideal of R

i986 : 
               1       4
o986 : Matrix R  <--- R

i987 :        p=5; --- p=2 behaves differently!
--R=ZZ/p[w,x,y,z];
R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;
www=res coker I;
peek(www)


i988 :        
i989 : 
o989 : Ideal of R

i990 : 
               1       4
o990 : Matrix R  <--- R

i991 : 
i992 : 
o992 = ChainComplex{cache => CacheTable{}                                   }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy-wz x3-w2y wy2-x2z y3-xz2 |

                               4                               4
                          1 : R  <--------------------------- R  : 2
                                    {2} | -x2 -wy -xz -y2 |
                                    {3} | y   z   0   0   |
                                    {3} | w   x   -y  -z  |
                                    {3} | 0   0   w   x   |

                               4                  1
                          2 : R  <-------------- R  : 3
                                    {4} | z  |
                                    {4} | -y |
                                    {4} | -x |
                                    {4} | w  |

                               1
                          3 : R  <----- 0 : 4
                                    0

i993 :        p=5; --- p=2 behaves differently!
--R=ZZ/p[w,x,y,z];
R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


i994 :        
i995 : 
o995 : Ideal of R

i996 : 
               1       4
o996 : Matrix R  <--- R

i997 : 
i998 : 
o998 = ChainComplex{cache => CacheTable{}                                   }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy-wz x3-w2y wy2-x2z y3-xz2 |

                               4                               4
                          1 : R  <--------------------------- R  : 2
                                    {2} | -x2 -wy -xz -y2 |
                                    {3} | y   z   0   0   |
                                    {3} | w   x   -y  -z  |
                                    {3} | 0   0   w   x   |

                               4                  1
                          2 : R  <-------------- R  : 3
                                    {4} | z  |
                                    {4} | -y |
                                    {4} | -x |
                                    {4} | w  |

                               1
                          3 : R  <----- 0 : 4
                                    0

i999 : stdio:89:12:(3):[2]: error: inducedMap: expected matrix to induce a well-defined map
     -- used 0.00222852 seconds

i1000 : 
o1000 = MutableHashTable{(2, 2) => 1}

i1001 :         p=2; --- p=2 behaves differently!
--R=ZZ/p[w,x,y,z];
R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


i1002 :         
i1003 : 
o1003 : Ideal of R

i1004 : 
                1       4
o1004 : Matrix R  <--- R

i1005 : 
i1006 : 
o1006 = ChainComplex{cache => CacheTable{}                                   }
                     Resolution => Resolution{...8...}
                     ring => R
                                1                                       4
                     dd => 0 : R  <----------------------------------- R  : 1
                                     | xy-wz x3-w2y wy2-x2z y3-xz2 |

                                4                               4
                           1 : R  <--------------------------- R  : 2
                                     {2} | -x2 -wy -xz -y2 |
                                     {3} | y   z   0   0   |
                                     {3} | w   x   -y  -z  |
                                     {3} | 0   0   w   x   |

                                4                  1
                           2 : R  <-------------- R  : 3
                                     {4} | z  |
                                     {4} | -y |
                                     {4} | -x |
                                     {4} | w  |

                                1
                           3 : R  <----- 0 : 4
                                     0

i1007 : stdio:89:12:(3):[2]: error: inducedMap: expected matrix to induce a well-defined map
     -- used 0.0017728 seconds

i1008 : 
o1008 = MutableHashTable{(2, 2) => 1}

i1009 :         p=2; --- p=2 behaves differently!
--R=ZZ/p[w,x,y,z];
R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


i1010 :         
i1011 : 
o1011 : Ideal of R

i1012 : 
                1       4
o1012 : Matrix R  <--- R

i1013 : 
i1014 : 
o1014 = ChainComplex{cache => CacheTable{}                                   }
                     Resolution => Resolution{...8...}
                     ring => R
                                1                                       4
                     dd => 0 : R  <----------------------------------- R  : 1
                                     | xy-wz x3-w2y wy2-x2z y3-xz2 |

                                4                               4
                           1 : R  <--------------------------- R  : 2
                                     {2} | -x2 -wy -xz -y2 |
                                     {3} | y   z   0   0   |
                                     {3} | w   x   -y  -z  |
                                     {3} | 0   0   w   x   |

                                4                  1
                           2 : R  <-------------- R  : 3
                                     {4} | z  |
                                     {4} | -y |
                                     {4} | -x |
                                     {4} | w  |

                                1
                           3 : R  <----- 0 : 4
                                     0

i1015 : stdio:89:12:(3):[2]: error: inducedMap: expected matrix to induce a well-defined map
     -- used 0.00275696 seconds

i1016 : 
o1016 = MutableHashTable{(2, 2) => 1}

i1017 :         p=2; --- p=2 behaves differently!
--R=ZZ/p[w,x,y,z];
R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


i1018 :         
i1019 : 
o1019 : Ideal of R

i1020 : 
                1       4
o1020 : Matrix R  <--- R

i1021 : 
i1022 : 
o1022 = ChainComplex{cache => CacheTable{}                                   }
                     Resolution => Resolution{...8...}
                     ring => R
                                1                                       4
                     dd => 0 : R  <----------------------------------- R  : 1
                                     | xy-wz x3-w2y wy2-x2z y3-xz2 |

                                4                               4
                           1 : R  <--------------------------- R  : 2
                                     {2} | -x2 -wy -xz -y2 |
                                     {3} | y   z   0   0   |
                                     {3} | w   x   -y  -z  |
                                     {3} | 0   0   w   x   |

                                4                  1
                           2 : R  <-------------- R  : 3
                                     {4} | z  |
                                     {4} | -y |
                                     {4} | -x |
                                     {4} | w  |

                                1
                           3 : R  <----- 0 : 4
                                     0

i1023 : stdio:89:12:(3):[2]: error: inducedMap: expected matrix to induce a well-defined map
     -- used 0.00175243 seconds

i1024 : 
o1024 = MutableHashTable{(2, 2) => 1}

i1025 :         p=2; --- p=2 behaves differently!
--R=ZZ/p[w,x,y,z];
R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


i1026 :         
i1027 : 
o1027 : Ideal of R

i1028 : 
                1       4
o1028 : Matrix R  <--- R

i1029 : 
i1030 : 
o1030 = ChainComplex{cache => CacheTable{}                                   }
                     Resolution => Resolution{...8...}
                     ring => R
                                1                                       4
                     dd => 0 : R  <----------------------------------- R  : 1
                                     | xy-wz x3-w2y wy2-x2z y3-xz2 |

                                4                               4
                           1 : R  <--------------------------- R  : 2
                                     {2} | -x2 -wy -xz -y2 |
                                     {3} | y   z   0   0   |
                                     {3} | w   x   -y  -z  |
                                     {3} | 0   0   w   x   |

                                4                  1
                           2 : R  <-------------- R  : 3
                                     {4} | z  |
                                     {4} | -y |
                                     {4} | -x |
                                     {4} | w  |

                                1
                           3 : R  <----- 0 : 4
                                     0

i1031 : stdio:89:12:(3):[2]: error: inducedMap: expected matrix to induce a well-defined map
     -- used 0.00202728 seconds

i1032 : 
o1032 = MutableHashTable{(2, 2) => 1}

i1033 :         p=2; --- p=2 behaves differently!
--R=ZZ/p[w,x,y,z];
R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


i1034 :         
i1035 : 
o1035 : Ideal of R

i1036 : 
                1       4
o1036 : Matrix R  <--- R

i1037 : 
i1038 : 
o1038 = ChainComplex{cache => CacheTable{}                                   }
                     Resolution => Resolution{...8...}
                     ring => R
                                1                                       4
                     dd => 0 : R  <----------------------------------- R  : 1
                                     | xy-wz x3-w2y wy2-x2z y3-xz2 |

                                4                               4
                           1 : R  <--------------------------- R  : 2
                                     {2} | -x2 -wy -xz -y2 |
                                     {3} | y   z   0   0   |
                                     {3} | w   x   -y  -z  |
                                     {3} | 0   0   w   x   |

                                4                  1
                           2 : R  <-------------- R  : 3
                                     {4} | z  |
                                     {4} | -y |
                                     {4} | -x |
                                     {4} | w  |

                                1
                           3 : R  <----- 0 : 4
                                     0

i1039 : stdio:89:12:(3):[2]: error: inducedMap: expected matrix to induce a well-defined map
     -- used 0.0158144 seconds

i1040 : 
o1040 = MutableHashTable{(2, 2) => 1}

i1041 :         p=2; --- p=2 behaves differently!
--R=ZZ/p[w,x,y,z];
R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


i1042 :         
i1043 : 
o1043 : Ideal of R

i1044 : 
                1       4
o1044 : Matrix R  <--- R

i1045 : 
i1046 : 
o1046 = ChainComplex{cache => CacheTable{}                                   }
                     Resolution => Resolution{...8...}
                     ring => R
                                1                                       4
                     dd => 0 : R  <----------------------------------- R  : 1
                                     | xy-wz x3-w2y wy2-x2z y3-xz2 |

                                4                               4
                           1 : R  <--------------------------- R  : 2
                                     {2} | -x2 -wy -xz -y2 |
                                     {3} | y   z   0   0   |
                                     {3} | w   x   -y  -z  |
                                     {3} | 0   0   w   x   |

                                4                  1
                           2 : R  <-------------- R  : 3
                                     {4} | z  |
                                     {4} | -y |
                                     {4} | -x |
                                     {4} | w  |

                                1
                           3 : R  <----- 0 : 4
                                     0

i1047 : stdio:89:12:(3):[2]: error: inducedMap: expected matrix to induce a well-defined map
     -- used 0.00221918 seconds

i1048 : 
o1048 = MutableHashTable{(2, 2) => 1}

i1049 :         restart;


--loadPackage "TestIdeals"
--loadPackage "BinomialEdgeIdeals"


---load "~/Dropbox/Macaulay2/My Libraries/my PosChar July 2019.m2"
---load "~/Dropbox/Macaulay2/My Libraries/randomObjects.m2"




--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------
--                      F U N C T I O N S 
--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------

--The following raises an ideal/matrix to a Frobenius power;
frobeniusPowerX=method()

frobeniusPowerX(Ideal,ZZ) := (I1,e1) ->(
     R1:=ring I1;
     p1:=char R1;
     local answer;
     G1:=first entries gens I1;
     if (#G1==0) then answer=ideal(0_R1) else answer=ideal(apply(G1, j->j^(p1^e1)));
     answer
);



frobeniusPowerX(Matrix,ZZ) := (M,e) ->(
R:=ring M;
p:=char R;
G:=entries M;
local i;
local j;
L:={};
apply(G, i->
{
	L=append(L,apply(i, j->j^(p^e)));
});
matrix L
);


--- Given matrices A, B with target R^alpha find all v\in R^alpha such that B v \in Image A
--- by computing a kernel
matrixColon= (A, B) ->(
---t0:=cpuTime();
assert(target(A)==target(B));
m:=rank source B;
w:=map(coker A, source B, B);
answer:=gens kernel w;
---print(cpuTime()-t0);
answer
)


--- Given a generating morphism U:coker(A) -> F(coker A), compute a generating root U:coker(L) -> F(coker L)
generatingRoot= (A,U) ->(
	R:=ring(A);
	L:=A;
	alpha:=rank target A;
	LL:=transpose matrix{toList(alpha:0_R)};
	while ((( L)%( LL))!=0) do
	{
		LL=L;
		L=L | matrixColon(frobeniusPowerX(L,1),U);
		L=mingens image L;
---		print("=================================================================");
---		print(L);
	};
	L
)



---compute a generating morphism for H^(dim R -i)_I(R)
---the output is (A,U) where U:coker(A) -> F(coker A) is the generating morphism
generatingMorphism= (I,i) ->(
	R:=ring(I); p:=char(R);
	Ip:=gens frobeniusPowerX(ideal I,1);
	M:=coker I;
	Mp:=coker Ip;
---	resM:=res M;
---	resMp:=res Mp;
	f:=inducedMap(M,Mp);
	resf:=res f;
	E:=Ext^i(f, R^1);
	(source E, E)
)


MfilterSequence =(A,l)->
(
    local f; local  answer; local   counter; local r ;
    R := ring I;
    V:=ideal(vars(R));
    T:=target(A);
--    answer=findMaximalRegularSequence(gens I);
    answer={};
    while ((#answer)<l) do
    {
--       print(#answer);
       J:=ideal(append(answer,0_R));
       B:=J*T+image(A);
       f=false;
       counter=0;
       while (not f) do
       {
--	   print(counter);
	   if (counter<dim(R)) then
	       r=V_counter
	   else
               r=randomElementInIdeal(((counter-dim(R))//20),V);
	   c1:=gens (B:r);
--	   print("c1",c1);
	   c2:=prune subquotient(c1, gens B);
--	   print("c2",c2);
	   c3:=radical annihilator c2;
--	   print("c3",c3);
	   c4:=(gens(V))%(gens(c3));
--	   print("c4",c4);
	   f=(c4==0);
	   counter=counter+1;
       };
       answer=append(answer, r);
---       print("MfilterSequence",l,dim(R),counter,answer);
    };
    answer
)


randomElementInIdeal=(d,I)->
(
    local answer;
    R := ring I;
    g:=gens I;
    n:=rank source gens I;
    m:=random(R^{n:d},R^1);
--    print(m,g);
    answer=entries (g*m);
    answer=first first answer;
--    print (answer);
    answer
)

   

saturation=(J,f,N)->
(
J:f^N
)

limClosure =(G,n)->
(
    if ((#G)<n) then 
    {
	print (" *** FATAL ERROR *** LimClosure, sequence too short");
	return;
    };
    R :=ring (G#0);
    p:=char(R);
    genI:= apply(0..(n-1), i->G#i);
    J:=ideal(genI);
    P:=toList genI;
    PP:=product(P);
    lastJ:=ideal(genI);
    f:=true;
    while (f) do
    {
---print(mingens J);	
    	J=frobeniusPowerX(J,1);
--	apply(P, z-> {J=J:z});
--    	J=J:PP;
    	J=saturation(J,PP,p-1); J=substitute(J,R);
	f= (gens(J)%gens(lastJ))!=0;
	if (f) then
	{
	    lastJ=J;
        };
---    	print(f,J);
    };  
    J
)
---limClosure((x_{1,1},x_{1,2},x_{1,3}),2)
---time limClosure(G,h)


lowLimClosure =(G,n)->
(
    R :=ring (G#0); 
    if ((#G)<n) then 
    {
	print (" *** FATAL ERROR *** lowLimClosure, sequence too short");
	return;
    }
    else if (n==1) then 
    {
	return ideal(0_R);
    };
    LC:=limClosure(G,n-1);
    g:=G#(n-1);
    saturate(LC,g)
)

---------------------------------------------------------------------------------------------------
---load "~/Dropbox/Rodney/LClibNew.m2"

--- Given a generating morphism U:A/B -> F(A/B), compute a generating root U:coker(L) -> F(coker L)
--- A, B, U matrices with same target
generatingSubquotientRoot= (A,B,U) ->(
	R:=ring(A);
	B0:=B;
	Ap:=frobeniusPowerX(A,1);
	Bp:=frobeniusPowerX(B0,1);
	assert ((U*A)%(Ap)==0);
	assert ((U*B0)%(Bp)==0);
	B1:= matrixColon(Bp, U);
	B1=matrix entries B1;
	B1= gens (intersect(image(B1), image(A)));
	while ((B1%B0)!=0) do
	{
	    B0=B1;
	    Bp=frobeniusPowerX(B0,1);
	    B1= matrixColon(Bp, U);
	    B1=matrix entries B1;
	    B1= gens (intersect(image(B1), image(A)));
	};
    (A,B1,prune subquotient(A,B1))
)



Lyubeznik = (A,U,i) ->(
local t; local answer; local F; local  L0; local  L1; 
local f; local  g; local  h; local  B; local  V; local  C;
local X; local Y;
local W;
R:=ring (A);
p:=char(R);
T:=target(A);
if (i>0) then
{
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    Q:=prune subquotient(gens B, gens C);
    if (Q==0) then
    {
	answer=0;
    }
    else
    {
	(X,Y,W)=generatingSubquotientRoot (gens B, gens C,V);
	if (W==0) then
	{
	    answer=0;
	}
    	else
    	{
    	    G1:=Hom(coker vars(R), W); 
--    	    answer=length(G1);   --- fails if G1 is not graded
    	    answer=rank source mingens G1;   
	};
    };
};
------------------------------------
if (i==0) then
{
    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
	if (X==0) then
	{
	    answer=0;
	}
    	else
    	{
     	    G1:=Hom(coker vars(R),  W); 
--    	    answer=length(G1);  --- fails if G1 is not graded
    	    answer=rank source mingens G1;   
	};
};
answer
)

LyubeznikTable  = (I) ->
(
    local i;  local  j;
    answer := new MutableHashTable;
    d:=dim coker I;
    R := ring I;
    n:= dim R;
    for j from 0 to d do
    {
	E:=generatingMorphism(I,n-j);
	if (not ((E#1)==0)) then
	{
	    U:=matrix entries (E#1);
	    A:=relations E#0; A=matrix entries A;
	    G:=generatingRoot(A,U);
    	    for i from 0 to j do
    	    {
	     	Z:=Lyubeznik (G,U,i);
	     	if (Z>0) then answer#(i,j)=Z;
---		print("***",i,j,Z);
    	    };
	};
    };
answer
)
















R=ZZ/2[A_1, A_2,B_1,B_2,C_1,C_2];
I=gens ideal(A_1*A_2,  B_1*B_2,  C_1*C_2,  A_1*B_1*C_1,   A_2*B_2*C_2 );
time LT=LyubeznikTable(I)
peek(LT)



--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------
--                       C A L C U L A T I O N S    A N D    E X A M P L E S
--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------
p=2; --- p=2 behaves differently!
--R=ZZ/p[w,x,y,z];
R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)

Macaulay2, version 1.19.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, InverseSystems, LLLBases, MinimalPrimes, PrimaryDecomposition, ReesAlgebra, Saturation, TangentCone

i1 :                                                                                                
o1 = frobeniusPowerX

o1 : MethodFunction

i2 :                                         
i3 :                                                                            
i4 :                                                             
o4 = matrixColon

o4 : FunctionClosure

i5 :                                                                                      
o5 = generatingRoot

o5 : FunctionClosure

i6 :                                                                                 
o6 = generatingMorphism

o6 : FunctionClosure

i7 :                                                                                                                                                                                                    
o7 = MfilterSequence

o7 : FunctionClosure

i8 :                                                                       
o8 = randomElementInIdeal

o8 : FunctionClosure

i9 :                               
o9 = saturation

o9 : FunctionClosure

i10 :                                                                                                                                                                                           
o10 = limClosure

o10 : FunctionClosure

i11 :                                                                                                                   
o11 = lowLimClosure

o11 : FunctionClosure

i12 :                                                                                                                                                       
o12 = generatingSubquotientRoot

o12 : FunctionClosure

i13 :                                                                                                                                                                                                                                                                                                                                                                                                                   stdio:295:13:(3): warning: local declaration of G1 shields variable with same name

o13 = Lyubeznik

o13 : FunctionClosure

i14 :                                                                                                                                                       
o14 = LyubeznikTable

o14 : FunctionClosure

i15 :                                                                                                 
i16 : 
              1       5
o16 : Matrix R  <--- R

i17 :      -- used 2.45235 seconds

o17 = MutableHashTable{...3...}

o17 : MutableHashTable

i18 : 
o18 = MutableHashTable{(0, 2) => 1}
                       (2, 3) => 1
                       (3, 3) => 1

i19 :                                                 
i20 :       
i21 : 
o21 : Ideal of R

i22 : 
              1       4
o22 : Matrix R  <--- R

i23 : 
i24 : 
o24 = ChainComplex{cache => CacheTable{}                                   }
                   Resolution => Resolution{...8...}
                   ring => R
                              1                                       4
                   dd => 0 : R  <----------------------------------- R  : 1
                                   | xy-wz x3-w2y wy2-x2z y3-xz2 |

                              4                               4
                         1 : R  <--------------------------- R  : 2
                                   {2} | -x2 -wy -xz -y2 |
                                   {3} | y   z   0   0   |
                                   {3} | w   x   -y  -z  |
                                   {3} | 0   0   w   x   |

                              4                  1
                         2 : R  <-------------- R  : 3
                                   {4} | z  |
                                   {4} | -y |
                                   {4} | -x |
                                   {4} | w  |

                              1
                         3 : R  <----- 0 : 4
                                   0

i25 : stdio:89:12:(3):[2]: error: inducedMap: expected matrix to induce a well-defined map
     -- used 0.00228963 seconds

i26 : 
o26 = MutableHashTable{(0, 2) => 1}
                       (2, 3) => 1
                       (3, 3) => 1

i27 :       I

o27 = | xy-wz y3-xz2 wy2-x2z x3-w2y |

              1       4
o27 : Matrix R  <--- R

i28 : quit

Process M2 interrupt

+ M2 --no-readline --print-width 98
Macaulay2, version 1.19.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, InverseSystems, LLLBases,
               MinimalPrimes, PrimaryDecomposition, ReesAlgebra, Saturation, TangentCone

i1 : restart;


--loadPackage "TestIdeals"
--loadPackage "BinomialEdgeIdeals"


---load "~/Dropbox/Macaulay2/My Libraries/my PosChar July 2019.m2"
---load "~/Dropbox/Macaulay2/My Libraries/randomObjects.m2"




--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------
--                      F U N C T I O N S 
--------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------

--The following raises an ideal/matrix to a Frobenius power;
frobeniusPowerX=method()

frobeniusPowerX(Ideal,ZZ) := (I1,e1) ->(
     R1:=ring I1;
     p1:=char R1;
     local answer;
     G1:=first entries gens I1;
     if (#G1==0) then answer=ideal(0_R1) else answer=ideal(apply(G1, j->j^(p1^e1)));
     answer
);



frobeniusPowerX(Matrix,ZZ) := (M,e) ->(
R:=ring M;
p:=char R;
G:=entries M;
local i;
local j;
L:={};
apply(G, i->
{
	L=append(L,apply(i, j->j^(p^e)));
});
matrix L
);


--- Given matrices A, B with target R^alpha find all v\in R^alpha such that B v \in Image A
--- by computing a kernel
matrixColon= (A, B) ->(
---t0:=cpuTime();
assert(target(A)==target(B));
m:=rank source B;
w:=map(coker A, source B, B);
answer:=gens kernel w;
---print(cpuTime()-t0);
answer
)


--- Given a generating morphism U:coker(A) -> F(coker A), compute a generating root U:coker(L) -> F(coker L)
generatingRoot= (A,U) ->(
	R:=ring(A);
	L:=A;
	alpha:=rank target A;
	LL:=transpose matrix{toList(alpha:0_R)};
	while ((( L)%( LL))!=0) do
	{
		LL=L;
		L=L | matrixColon(frobeniusPowerX(L,1),U);
		L=mingens image L;
---		print("=================================================================");
---		print(L);
	};
	L
)



---compute a generating morphism for H^(dim R -i)_I(R)
---the output is (A,U) where U:coker(A) -> F(coker A) is the generating morphism
generatingMorphism= (I,i) ->(
	R:=ring(I); p:=char(R);
	Ip:=gens frobeniusPowerX(ideal I,1);
	M:=coker I;
	Mp:=coker Ip;
---	resM:=res M;
---	resMp:=res Mp;
	f:=inducedMap(M,Mp);
	resf:=res f;
	E:=Ext^i(f, R^1);
	(source E, E)
)


MfilterSequence =(A,l)->
(
    local f; local  answer; local   counter; local r ;
    R := ring I;
    V:=ideal(vars(R));
    T:=target(A);
--    answer=findMaximalRegularSequence(gens I);
    answer={};
    while ((#answer)<l) do
    {
--       print(#answer);
       J:=ideal(append(answer,0_R));
       B:=J*T+image(A);
       f=false;
       counter=0;
       while (not f) do
       {
--	   print(counter);
	   if (counter<dim(R)) then
	       r=V_counter
	   else
               r=randomElementInIdeal(((counter-dim(R))//20),V);
	   c1:=gens (B:r);
--	   print("c1",c1);
	   c2:=prune subquotient(c1, gens B);
--	   print("c2",c2);
	   c3:=radical annihilator c2;
--	   print("c3",c3);
	   c4:=(gens(V))%(gens(c3));
--	   print("c4",c4);
	   f=(c4==0);
	   counter=counter+1;
       };
       answer=append(answer, r);
---       print("MfilterSequence",l,dim(R),counter,answer);
    };
    answer
)


randomElementInIdeal=(d,I)->
(
    local answer;
    R := ring I;
    g:=gens I;
    n:=rank source gens I;
    m:=random(R^{n:d},R^1);
--    print(m,g);
    answer=entries (g*m);
    answer=first first answer;
--    print (answer);
    answer
)

   

saturation=(J,f,N)->
(
J:f^N
)

limClosure =(G,n)->
(
    if ((#G)<n) then 
    {
	print (" *** FATAL ERROR *** LimClosure, sequence too short");
	return;
    };
    R :=ring (G#0);
    p:=char(R);
    genI:= apply(0..(n-1), i->G#i);
    J:=ideal(genI);
    P:=toList genI;
    PP:=product(P);
    lastJ:=ideal(genI);
    f:=true;
    while (f) do
    {
---print(mingens J);	
    	J=frobeniusPowerX(J,1);
--	apply(P, z-> {J=J:z});
--    	J=J:PP;
    	J=saturation(J,PP,p-1); J=substitute(J,R);
	f= (gens(J)%gens(lastJ))!=0;
	if (f) then
	{
	    lastJ=J;
        };
---    	print(f,J);
    };  
    J
)
---limClosure((x_{1,1},x_{1,2},x_{1,3}),2)
---time limClosure(G,h)


lowLimClosure =(G,n)->
(
    R :=ring (G#0); 
    if ((#G)<n) then 
    {
	print (" *** FATAL ERROR *** lowLimClosure, sequence too short");
	return;
    }
    else if (n==1) then 
    {
	return ideal(0_R);
    };
    LC:=limClosure(G,n-1);
    g:=G#(n-1);
    saturate(LC,g)
)

---------------------------------------------------------------------------------------------------
---load "~/Dropbox/Rodney/LClibNew.m2"

--- Given a generating morphism U:A/B -> F(A/B), compute a generating root U:coker(L) -> F(coker L)
--- A, B, U matrices with same target
generatingSubquotientRoot= (A,B,U) ->(
	R:=ring(A);
	B0:=B;
	Ap:=frobeniusPowerX(A,1);
	Bp:=frobeniusPowerX(B0,1);
	assert ((U*A)%(Ap)==0);
	assert ((U*B0)%(Bp)==0);
	B1:= matrixColon(Bp, U);
	B1=matrix entries B1;
	B1= gens (intersect(image(B1), image(A)));
	while ((B1%B0)!=0) do
	{
	    B0=B1;
	    Bp=frobeniusPowerX(B0,1);
	    B1= matrixColon(Bp, U);
	    B1=matrix entries B1;
	    B1= gens (intersect(image(B1), image(A)));
	};
    (A,B1,prune subquotient(A,B1))
)



Lyubeznik = (A,U,i) ->(
local t; local answer; local F; local  L0; local  L1; 
local f; local  g; local  h; local  B; local  V; local  C;
local X; local Y;
local W;
R:=ring (A);
p:=char(R);
T:=target(A);
if (i>0) then
{
    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    Q:=prune subquotient(gens B, gens C);
    if (Q==0) then
    {
	answer=0;
    }
    else
    {
	(X,Y,W)=generatingSubquotientRoot (gens B, gens C,V);
	if (W==0) then
	{
	    answer=0;
	}
    	else
    	{
    	    G1:=Hom(coker vars(R), W); 
--    	    answer=length(G1);   --- fails if G1 is not graded
    	    answer=rank source mingens G1;   
	};
    };
};
------------------------------------
if (i==0) then
{
    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
	if (X==0) then
	{
	    answer=0;
	}
    	else
    	{
     	    G1:=Hom(coker vars(R),  W); 
--    	    answer=length(G1);  --- fails if G1 is not graded
    	    answer=rank source mingens G1;   
	};
};
answer
)

LyubeznikTable  = (I) ->
(
    local i;  local  j;
    answer := new MutableHashTable;
    d:=dim coker I;
    R := ring I;
    n:= dim R;
    for j from 0 to d do
    {
	E:=generatingMorphism(I,n-j);
	if (not ((E#1)==0)) then
	{
	    U:=matrix entries (E#1);
	    A:=relations E#0; A=matrix entries A;
	    G:=generatingRoot(A,U);
    	    for i from 0 to j do
    	    {
	     	Z:=Lyubeznik (G,U,i);
	     	if (Z>0) then answer#(i,j)=Z;
---		print("***",i,j,Z);
    	    };
	};
    };
answer
)










Macaulay2, version 1.19.1
with packages: ConwayPolynomials, Elimination, IntegralClosure, InverseSystems, LLLBases,
               MinimalPrimes, PrimaryDecomposition, ReesAlgebra, Saturation, TangentCone

i1 :                                                                                                
o1 = frobeniusPowerX

o1 : MethodFunction

i2 :                                         
i3 :                                                                            
i4 :                                                             
o4 = matrixColon

o4 : FunctionClosure

i5 :                                                                                      
o5 = generatingRoot

o5 : FunctionClosure

i6 :                                                                                 
o6 = generatingMorphism

o6 : FunctionClosure

i7 :                                                                                                                                                                                                    
o7 = MfilterSequence

o7 : FunctionClosure

i8 :                                                                       
o8 = randomElementInIdeal

o8 : FunctionClosure

i9 :                               
o9 = saturation

o9 : FunctionClosure

i10 :                                                                                                                                                                                           
o10 = limClosure

o10 : FunctionClosure

i11 :                                                                                                                   
o11 = lowLimClosure

o11 : FunctionClosure

i12 :                                                                                                                                                       
o12 = generatingSubquotientRoot

o12 : FunctionClosure

i13 :                                                                                                                                                                                                                                                                                                                                                                                                                   stdio:295:13:(3): warning: local declaration of G1 shields variable with same name

o13 = Lyubeznik

o13 : FunctionClosure

i14 :                                                                                                                                                       
o14 = LyubeznikTable

o14 : FunctionClosure

i15 :                                                             p=2; --- p=2 behaves differently!
--R=ZZ/p[w,x,y,z];
R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;


i16 :       
i17 : 
o17 : Ideal of R

i18 : 
              1       4
o18 : Matrix R  <--- R

i19 :       time LT=LyubeznikTable(I)
peek(LT)

stdio:89:12:(3):[2]: error: inducedMap: expected matrix to induce a well-defined map
     -- used 0.00289869 seconds

i20 : 
o20 = LT

i21 :       p=2; --- p=2 behaves differently!
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


i22 : 
i23 :       
o23 : Ideal of R

i24 : 
              1       4
o24 : Matrix R  <--- R

i25 : 
i26 : 
o26 = ChainComplex{cache => CacheTable{}                                   }
                   Resolution => Resolution{...8...}
                   ring => R
                              1                                       4
                   dd => 0 : R  <----------------------------------- R  : 1
                                   | xy+wz x3+w2y wy2+x2z y3+xz2 |

                              4                           4
                         1 : R  <----------------------- R  : 2
                                   {2} | x2 wy xz y2 |
                                   {3} | y  z  0  0  |
                                   {3} | w  x  y  z  |
                                   {3} | 0  0  w  x  |

                              4                 1
                         2 : R  <------------- R  : 3
                                   {4} | z |
                                   {4} | y |
                                   {4} | x |
                                   {4} | w |

                              1
                         3 : R  <----- 0 : 4
                                   0

i27 :      -- used 0.17983 seconds

o27 = MutableHashTable{...1...}

o27 : MutableHashTable

i28 : 
o28 = MutableHashTable{(2, 2) => 1}

i29 :       p=5; --- p=2 behaves differently!
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


i30 : 
i31 :       
o31 : Ideal of R

i32 : 
              1       4
o32 : Matrix R  <--- R

i33 : 
i34 : 
o34 = ChainComplex{cache => CacheTable{}                                   }
                   Resolution => Resolution{...8...}
                   ring => R
                              1                                       4
                   dd => 0 : R  <----------------------------------- R  : 1
                                   | xy-wz x3-w2y wy2-x2z y3-xz2 |

                              4                               4
                         1 : R  <--------------------------- R  : 2
                                   {2} | -x2 -wy -xz -y2 |
                                   {3} | y   z   0   0   |
                                   {3} | w   x   -y  -z  |
                                   {3} | 0   0   w   x   |

                              4                  1
                         2 : R  <-------------- R  : 3
                                   {4} | z  |
                                   {4} | -y |
                                   {4} | -x |
                                   {4} | w  |

                              1
                         3 : R  <----- 0 : 4
                                   0

i35 :      -- used 0.174836 seconds

o35 = MutableHashTable{...1...}

o35 : MutableHashTable

i36 : 
o36 = MutableHashTable{(2, 2) => 1}

i37 :       E2=generatingMorphism(I,2)


o37 = (cokernel {-3} | y  w  0 x 0 |, {-15} |
                {-3} | -z -x y 0 w |  {-15} |
                {-3} | 0  0  z y x |  {-15} |
      --------------------------------------------------------------------------------------------
      w3x4y4z+w4x3y3z2+w4x4z4                                                                 
      wx5y4z2+x7y2z3+w2x4y3z3+w4xy4z3+wx6yz4+w3x3y2z4+w2x5z5+w4x2yz5                          
      -x3y9-wx2y8z-x4y6z2-w2xy7z2-wx3y5z3-w3y6z3-x5y3z4-w2x2y4z4-wx4y2z5-w3xy3z5-x6z6-w2x3yz6-
      --------------------------------------------------------------------------------------------
                    w4x3y4z+w4x4yz3                                                          
                    x7y3z2+w2x4y4z2+wx6y2z3+w3x3y3z3+x8z4+w2x5yz4+w4x2y2z4+w3x4z5            
      w4y2z6-w3x2z7 -wx2y9-x4y7z-w2xy8z-wx3y6z2-w3y7z2-x5y4z3-w2x2y5z3-wx4y3z4-w3xy4z4-x6yz5-
      --------------------------------------------------------------------------------------------
                                         
                                         
      w2x3y2z5-w4y3z5-wx5z6-w3x2yz6-w4xz7
      --------------------------------------------------------------------------------------------
      -w4x4y2z2                                                                               
      -x7y4z-wx6y3z2-w3x3y4z2-x8yz3-w2x5y2z3-w4x2y3z3-wx7z4-w3x4yz4-w4x3z5                    
      x4y8+w2xy9+wx3y7z+w3y8z+w2x2y6z2+wx4y4z3+w3xy5z3+x6y2z4+w2x3y3z4+w4y4z4+wx5yz5+w3x2y2z5+
      --------------------------------------------------------------------------------------------
                         |)
                         |
      w2x4z6+w4xyz6+w5z7 |

o37 : Sequence

i38 :       p=2; --- p=2 behaves differently!
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


i39 : 
i40 :       
o40 : Ideal of R

i41 : 
              1       4
o41 : Matrix R  <--- R

i42 : 
i43 : 
o43 = ChainComplex{cache => CacheTable{}                                   }
                   Resolution => Resolution{...8...}
                   ring => R
                              1                                       4
                   dd => 0 : R  <----------------------------------- R  : 1
                                   | xy+wz x3+w2y wy2+x2z y3+xz2 |

                              4                           4
                         1 : R  <----------------------- R  : 2
                                   {2} | x2 wy xz y2 |
                                   {3} | y  z  0  0  |
                                   {3} | w  x  y  z  |
                                   {3} | 0  0  w  x  |

                              4                 1
                         2 : R  <------------- R  : 3
                                   {4} | z |
                                   {4} | y |
                                   {4} | x |
                                   {4} | w |

                              1
                         3 : R  <----- 0 : 4
                                   0

i44 :      -- used 0.169329 seconds

o44 = MutableHashTable{...1...}

o44 : MutableHashTable

i45 : 
o45 = MutableHashTable{(2, 2) => 1}

i46 :       E2=generatingMorphism(I,2)
A=matrix entries relations E2#0
T=target A
U=matrix entries E2#1


o46 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o46 : Sequence

i47 : 
o47 = | y w 0 x 0 |
      | z x y 0 w |
      | 0 0 z y x |

              3       5
o47 : Matrix R  <--- R

i48 : 
       3
o48 = R

o48 : R-module, free

i49 : 
o49 = | wxz    wxy     0       |
      | wyz    x2z     x2y+wxz |
      | y3+xz2 xyz+wz2 xy2+wyz |

              3       3
o49 : Matrix R  <--- R

i50 :       A

o50 = | y w 0 x 0 |
      | z x y 0 w |
      | 0 0 z y x |

              3       5
o50 : Matrix R  <--- R

i51 : F=MfilterSequence(A,3)


o51 = {w, z, w}

o51 : List

i52 :       F=MfilterSequence(A,3)


o52 = {w, z, w}

o52 : List

i53 :       F=MfilterSequence(A,3)


o53 = {w, z, w}

o53 : List

i54 :       F=MfilterSequence(A,3)


o54 = {w, z, w}

o54 : List

i55 :       F=MfilterSequence(A,3)


o55 = {w, z, w}

o55 : List

i56 :       F=MfilterSequence(A,3)


o56 = {w, z, w}

o56 : List

i57 :       F=MfilterSequence(A,3)


o57 = {w, z, w}

o57 : List

i58 :       F=MfilterSequence(A,3)


o58 = {w, z, w}

o58 : List

i59 :       F=MfilterSequence(A,3)


o59 = {w, z, w}

o59 : List

i60 :       F=MfilterSequence(A,3)


o60 = {w, z, w}

o60 : List

i61 :       F=MfilterSequence(A,3)


o61 = {w, z, w}

o61 : List

i62 :       F=MfilterSequence(A,3)


o62 = {w, z, w}

o62 : List

i63 :       F=MfilterSequence(A,3)


o63 = {w, z, w}

o63 : List

i64 :       F=MfilterSequence(A,3)


o64 = {w, z, w}

o64 : List

i65 :       F=MfilterSequence(A,3)


o65 = {w, z, w}

o65 : List

i66 :       F=MfilterSequence(A,3)


o66 = {w, z, w}

o66 : List

i67 :       F=MfilterSequence(A,3)


o67 = {w, z, w}

o67 : List

i68 :       F={w,z,w};
------------------------------------
i=0

---    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    -- im B = im C!
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
assert (X!=0);
     	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
    print(answer, prune subquotient (gens B, gens C));
    


i69 :       
o69 = 0

i70 :             
o70 : Ideal of R

i71 : 
o71 : Ideal of R

i72 : 
i73 : 
i74 : 
i75 : 
i76 : 
              3       3
o76 : Matrix R  <--- R

i77 : 
i78 :       
i79 : 
i80 : 
i81 : 
i82 : (0, 0)

i83 :             i=1;
---    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
    assert (X!=0);
     	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
    print(answer, prune subquotient (gens B, gens C));



i84 :       
o84 : Ideal of R

i85 : 
o85 : Ideal of R

i86 : 
i87 : 
i88 : 
i89 : 
i90 : 
              3       3
o90 : Matrix R  <--- R

i91 : 
i92 : 
i93 : 
i94 : 
i95 : 
i96 : (0, 0)

i97 :             i=2;
---    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
    (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
    assert (X!=0);
     	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   
    print(answer, prune subquotient (gens B, gens C));




i98 :       
o98 : Ideal of R

i99 : 
o99 : Ideal of R

i100 : 
i101 : 
i102 : 
i103 : 
i104 : 
               3       3
o104 : Matrix R  <--- R

i105 : 
i106 : 
i107 : 
i108 : 
i109 : 
i110 : (1, cokernel | z y w 0 0 0 0 0 x 0 0 |)
             | 0 0 0 z y x w 0 0 0 0 |
             | 0 0 0 0 0 0 0 z y x w |

i111 :        W                     W              

o111 = cokernel | z y w 0 x 0 0 |
                | 0 0 0 z y x w |

                              2
o111 : R-module, quotient of R

i112 : 

E2=generatingMorphism(I,2)
A=matrix entries relations E2#0
T=target A
U=matrix entries E2#1

              
o112 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o112 : Sequence

i113 : 
o113 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o113 : Matrix R  <--- R

i114 : 
        3
o114 = R

o114 : R-module, free

i115 : 
o115 = | wxz    wxy     0       |
       | wyz    x2z     x2y+wxz |
       | y3+xz2 xyz+wz2 xy2+wyz |

               3       3
o115 : Matrix R  <--- R

i116 :        p=11; --- p=2 behaves differently!
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


i117 : 
i118 :        
o118 : Ideal of R

i119 : 
               1       4
o119 : Matrix R  <--- R

i120 : 
i121 : 
o121 = ChainComplex{cache => CacheTable{}                                   }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy-wz x3-w2y wy2-x2z y3-xz2 |

                               4                               4
                          1 : R  <--------------------------- R  : 2
                                    {2} | -x2 -wy -xz -y2 |
                                    {3} | y   z   0   0   |
                                    {3} | w   x   -y  -z  |
                                    {3} | 0   0   w   x   |

                               4                  1
                          2 : R  <-------------- R  : 3
                                    {4} | z  |
                                    {4} | -y |
                                    {4} | -x |
                                    {4} | w  |

                               1
                          3 : R  <----- 0 : 4
                                    0

i122 :      -- used 0.1907 seconds

o122 = MutableHashTable{...1...}

o122 : MutableHashTable

i123 : 
o123 = MutableHashTable{(2, 2) => 1}

i124 :        E2=generatingMorphism(I,2)
A=matrix entries relations E2#0
T=target A
U=matrix entries E2#1


o124 = (cokernel {-3} | y  w  0 x 0 |, {-33} |
                 {-3} | -z -x y 0 w |  {-33} |
                 {-3} | 0  0  z y x |  {-33} |
       -------------------------------------------------------------------------------------------
       w9x8y10z3+w8x10y8z4+w10x7y9z4+w9x9y7z5+w10x8y6z6+w9x10y4z7+w10x9y3z8+w10x10z10             
       wx15y10z4+x17y8z5+w2x14y9z5+w4x11y10z5+wx16y7z6+w3x13y8z6+w5x10y9z6+w7x7y10z6+x18y5z7+w2x15
       -x9y21-wx8y20z-w3x5y21z-x10y18z2-w2x7y19z2-w4x4y20z2-w6xy21z2-wx9y17z3-w3x6y18z3-w5x3y19z3-
       -------------------------------------------------------------------------------------------
                                                                                                  
       y6z7+w4x12y7z7+w6x9y8z7+w8x6y9z7+w10x3y10z7+wx17y4z8+w3x14y5z8+w5x11y6z8+w7x8y7z8+w9x5y8z8+
       w7y20z3-w2x8y16z4-w4x5y17z4-w6x2y18z4-wx10y14z5-w3x7y15z5-w5x4y16z5-w7xy17z5-w2x9y13z6-w4x6
       -------------------------------------------------------------------------------------------
                                                                                                  
       x19y2z9+w2x16y3z9+w4x13y4z9+w6x10y5z9+w8x7y6z9+w10x4y7z9+wx18yz10+w3x15y2z10+w5x12y3z10+w7x
       y14z6-w6x3y15z6-w8y16z6-w3x8y12z7-w5x5y13z7-w7x2y14z7-x13y9z8-w2x10y10z8-w4x7y11z8-w6x4y12z
       -------------------------------------------------------------------------------------------
                                                                                              
       9y4z10+w9x6y5z10+w2x17z11+w4x14yz11+w6x11y2z11+w8x8y3z11+w10x5y4z11+w5x13z12+w7x10yz12+
       8-w8xy13z8-wx12y8z9-w3x9y9z9-w5x6y10z9-w7x3y11z9-w9y12z9-x14y6z10-w2x11y7z10-w4x8y8z10-
       -------------------------------------------------------------------------------------------
                                                                                                  
       w9x7y2z12+w8x9z13+w10x6yz13                                                                
       w6x5y9z10-w8x2y10z10-wx13y5z11-w3x10y6z11-w5x7y7z11-w7x4y8z11-w9xy9z11-x15y3z12-w2x12y4z12-
       -------------------------------------------------------------------------------------------
                                                                                                 
                                                                                                 
       w4x9y5z12-w6x6y6z12-w8x3y7z12-w10y8z12-wx14y2z13-w3x11y3z13-w5x8y4z13-w7x5y5z13-w9x2y6z13-
       -------------------------------------------------------------------------------------------
                                                                                             
                                                                                             
       x16z14-w2x13yz14-w4x10y2z14-w6x7y3z14-w8x4y4z14-w10xy5z14-w3x12z15-w5x9yz15-w7x6y2z15-
       -------------------------------------------------------------------------------------------
                                                                             
                                                                             
       w9x3y3z15-w11y4z15-w6x8z16-w8x5yz16-w10x2y2z16-w9x4z17-w11xyz17-w12z18
       -------------------------------------------------------------------------------------------
       w8x10y9z3+w10x7y10z3+w9x9y8z4+w10x8y7z5+w9x10y5z6+w10x9y4z7+w10x10yz9                      
       x17y9z4+w2x14y10z4+wx16y8z5+w3x13y9z5+w5x10y10z5+x18y6z6+w2x15y7z6+w4x12y8z6+w6x9y9z6+w8x6y
       -wx8y21-x10y19z-w2x7y20z-w4x4y21z-wx9y18z2-w3x6y19z2-w5x3y20z2-w7y21z2-w2x8y17z3-w4x5y18z3-
       -------------------------------------------------------------------------------------------
                                                                                      
       10z6+wx17y5z7+w3x14y6z7+w5x11y7z7+w7x8y8z7+w9x5y9z7+x19y3z8+w2x16y4z8+w4x13y5z8
       w6x2y19z3-wx10y15z4-w3x7y16z4-w5x4y17z4-w7xy18z4-w2x9y14z5-w4x6y15z5-w6x3y16z5-
       -------------------------------------------------------------------------------------------
                                                                                    
       +w6x10y6z8+w8x7y7z8+w10x4y8z8+wx18y2z9+w3x15y3z9+w5x12y4z9+w7x9y5z9+w9x6y6z9+
       w8y17z5-w3x8y13z6-w5x5y14z6-w7x2y15z6-x13y10z7-w2x10y11z7-w4x7y12z7-w6x4y13z7
       -------------------------------------------------------------------------------------------
                                                        
       x20z10+w2x17yz10+w4x14y2z10+w6x11y3z10+w8x8y4z10+
       -w8xy14z7-wx12y9z8-w3x9y10z8-w5x6y11z8-w7x3y12z8-
       -------------------------------------------------------------------------------------------
                                                                                                  
       w10x5y5z10+w3x16z11+w5x13yz11+w7x10y2z11+w9x7y3z11+w6x12z12+w8x9yz12+w10x6y2z12+w9x8z13    
       w9y13z8-x14y7z9-w2x11y8z9-w4x8y9z9-w6x5y10z9-w8x2y11z9-wx13y6z10-w3x10y7z10-w5x7y8z10-w7x4y
       -------------------------------------------------------------------------------------------
                                                                                           
                                                                                           
       9z10-w9xy10z10-x15y4z11-w2x12y5z11-w4x9y6z11-w6x6y7z11-w8x3y8z11-w10y9z11-wx14y3z12-
       -------------------------------------------------------------------------------------------
                                                                                                  
                                                                                                  
       w3x11y4z12-w5x8y5z12-w7x5y6z12-w9x2y7z12-x16yz13-w2x13y2z13-w4x10y3z13-w6x7y4z13-w8x4y5z13-
       -------------------------------------------------------------------------------------------
                                                                                            
                                                                                            
       w10xy6z13-wx15z14-w3x12yz14-w5x9y2z14-w7x6y3z14-w9x3y4z14-w11y5z14-w4x11z15-w6x8yz15-
       -------------------------------------------------------------------------------------------
                                                                       
                                                                       
       w8x5y2z15-w10x2y3z15-w7x7z16-w9x4yz16-w11xy2z16-w10x3z17-w12yz17
       -------------------------------------------------------------------------------------------
       -w8x10y10z2-w9x9y9z3-w10x8y8z4-w9x10y6z5-w10x9y5z6-w10x10y2z8                              
       -x17y10z3-wx16y9z4-w3x13y10z4-x18y7z5-w2x15y8z5-w4x12y9z5-w6x9y10z5-wx17y6z6-w3x14y7z6-w5x1
       x10y20+w2x7y21+wx9y19z+w3x6y20z+w5x3y21z+w2x8y18z2+w4x5y19z2+w6x2y20z2+wx10y16z3+w3x7y17z3+
       -------------------------------------------------------------------------------------------
                                                                                                  
       1y8z6-w7x8y9z6-w9x5y10z6-x19y4z7-w2x16y5z7-w4x13y6z7-w6x10y7z7-w8x7y8z7-w10x4y9z7-wx18y3z8-
       w5x4y18z3+w7xy19z3+w2x9y15z4+w4x6y16z4+w6x3y17z4+w8y18z4+w3x8y14z5+w5x5y15z5+w7x2y16z5+w2x1
       -------------------------------------------------------------------------------------------
                                                                                           
       w3x15y4z8-w5x12y5z8-w7x9y6z8-w9x6y7z8-x20yz9-w2x17y2z9-w4x14y3z9-w6x11y4z9-w8x8y5z9-
       0y12z6+w4x7y13z6+w6x4y14z6+w8xy15z6+wx12y10z7+w3x9y11z7+w5x6y12z7+w7x3y13z7+w9y14z7+
       -------------------------------------------------------------------------------------------
                                             
       w10x5y6z9-wx19z10-w3x16yz10-w5x13y2z10
       x14y8z8+w2x11y9z8+w4x8y10z8+w6x5y11z8+
       -------------------------------------------------------------------------------------------
                                                                                                  
       -w7x10y3z10-w9x7y4z10-w4x15z11-w6x12yz11-w8x9y2z11-w10x6y3z11-w7x11z12-w9x8yz12-w10x7z13   
       w8x2y12z8+wx13y7z9+w3x10y8z9+w5x7y9z9+w7x4y10z9+w9xy11z9+x15y5z10+w2x12y6z10+w4x9y7z10+w6x6
       -------------------------------------------------------------------------------------------
                                                                                             
                                                                                             
       y8z10+w8x3y9z10+w10y10z10+wx14y4z11+w3x11y5z11+w5x8y6z11+w7x5y7z11+w9x2y8z11+x16y2z12+
       -------------------------------------------------------------------------------------------
                                                                                                  
                                                                                                  
       w2x13y3z12+w4x10y4z12+w6x7y5z12+w8x4y6z12+w10xy7z12+wx15yz13+w3x12y2z13+w5x9y3z13+w7x6y4z13
       -------------------------------------------------------------------------------------------
                                                                                               
                                                                                               
       +w9x3y5z13+w11y6z13+w2x14z14+w4x11yz14+w6x8y2z14+w8x5y3z14+w10x2y4z14+w5x10z15+w7x7yz15+
       -------------------------------------------------------------------------------------------
                                                               |)
                                                               |
       w9x4y2z15+w11xy3z15+w8x6z16+w10x3yz16+w12y2z16+w11x2z17 |

o124 : Sequence

i125 : 
o125 = | y  w  0 x 0 |
       | -z -x y 0 w |
       | 0  0  z y x |

               3       5
o125 : Matrix R  <--- R

i126 : 
        3
o126 = R

o126 : R-module, free

i127 : 
o127 = | w9x8y10z3+w8x10y8z4+w10x7y9z4+w9x9y7z5+w10x8y6z6+w9x10y4z7+w10x9y3z8+w10x10z10           
       | wx15y10z4+x17y8z5+w2x14y9z5+w4x11y10z5+wx16y7z6+w3x13y8z6+w5x10y9z6+w7x7y10z6+x18y5z7+w2x
       | -x9y21-wx8y20z-w3x5y21z-x10y18z2-w2x7y19z2-w4x4y20z2-w6xy21z2-wx9y17z3-w3x6y18z3-w5x3y19z
       -------------------------------------------------------------------------------------------
                                                                                                  
       15y6z7+w4x12y7z7+w6x9y8z7+w8x6y9z7+w10x3y10z7+wx17y4z8+w3x14y5z8+w5x11y6z8+w7x8y7z8+w9x5y8z
       3-w7y20z3-w2x8y16z4-w4x5y17z4-w6x2y18z4-wx10y14z5-w3x7y15z5-w5x4y16z5-w7xy17z5-w2x9y13z6-w4
       -------------------------------------------------------------------------------------------
                                                                                                  
       8+x19y2z9+w2x16y3z9+w4x13y4z9+w6x10y5z9+w8x7y6z9+w10x4y7z9+wx18yz10+w3x15y2z10+w5x12y3z10+w
       x6y14z6-w6x3y15z6-w8y16z6-w3x8y12z7-w5x5y13z7-w7x2y14z7-x13y9z8-w2x10y10z8-w4x7y11z8-w6x4y1
       -------------------------------------------------------------------------------------------
                                                                                                
       7x9y4z10+w9x6y5z10+w2x17z11+w4x14yz11+w6x11y2z11+w8x8y3z11+w10x5y4z11+w5x13z12+w7x10yz12+
       2z8-w8xy13z8-wx12y8z9-w3x9y9z9-w5x6y10z9-w7x3y11z9-w9y12z9-x14y6z10-w2x11y7z10-w4x8y8z10-
       -------------------------------------------------------------------------------------------
                                                                                                  
       w9x7y2z12+w8x9z13+w10x6yz13                                                                
       w6x5y9z10-w8x2y10z10-wx13y5z11-w3x10y6z11-w5x7y7z11-w7x4y8z11-w9xy9z11-x15y3z12-w2x12y4z12-
       -------------------------------------------------------------------------------------------
                                                                                                 
                                                                                                 
       w4x9y5z12-w6x6y6z12-w8x3y7z12-w10y8z12-wx14y2z13-w3x11y3z13-w5x8y4z13-w7x5y5z13-w9x2y6z13-
       -------------------------------------------------------------------------------------------
                                                                                             
                                                                                             
       x16z14-w2x13yz14-w4x10y2z14-w6x7y3z14-w8x4y4z14-w10xy5z14-w3x12z15-w5x9yz15-w7x6y2z15-
       -------------------------------------------------------------------------------------------
                                                                             
                                                                             
       w9x3y3z15-w11y4z15-w6x8z16-w8x5yz16-w10x2y2z16-w9x4z17-w11xyz17-w12z18
       -------------------------------------------------------------------------------------------
       w8x10y9z3+w10x7y10z3+w9x9y8z4+w10x8y7z5+w9x10y5z6+w10x9y4z7+w10x10yz9                      
       x17y9z4+w2x14y10z4+wx16y8z5+w3x13y9z5+w5x10y10z5+x18y6z6+w2x15y7z6+w4x12y8z6+w6x9y9z6+w8x6y
       -wx8y21-x10y19z-w2x7y20z-w4x4y21z-wx9y18z2-w3x6y19z2-w5x3y20z2-w7y21z2-w2x8y17z3-w4x5y18z3-
       -------------------------------------------------------------------------------------------
                                                                                      
       10z6+wx17y5z7+w3x14y6z7+w5x11y7z7+w7x8y8z7+w9x5y9z7+x19y3z8+w2x16y4z8+w4x13y5z8
       w6x2y19z3-wx10y15z4-w3x7y16z4-w5x4y17z4-w7xy18z4-w2x9y14z5-w4x6y15z5-w6x3y16z5-
       -------------------------------------------------------------------------------------------
                                                                                    
       +w6x10y6z8+w8x7y7z8+w10x4y8z8+wx18y2z9+w3x15y3z9+w5x12y4z9+w7x9y5z9+w9x6y6z9+
       w8y17z5-w3x8y13z6-w5x5y14z6-w7x2y15z6-x13y10z7-w2x10y11z7-w4x7y12z7-w6x4y13z7
       -------------------------------------------------------------------------------------------
                                                        
       x20z10+w2x17yz10+w4x14y2z10+w6x11y3z10+w8x8y4z10+
       -w8xy14z7-wx12y9z8-w3x9y10z8-w5x6y11z8-w7x3y12z8-
       -------------------------------------------------------------------------------------------
                                                                                                  
       w10x5y5z10+w3x16z11+w5x13yz11+w7x10y2z11+w9x7y3z11+w6x12z12+w8x9yz12+w10x6y2z12+w9x8z13    
       w9y13z8-x14y7z9-w2x11y8z9-w4x8y9z9-w6x5y10z9-w8x2y11z9-wx13y6z10-w3x10y7z10-w5x7y8z10-w7x4y
       -------------------------------------------------------------------------------------------
                                                                                           
                                                                                           
       9z10-w9xy10z10-x15y4z11-w2x12y5z11-w4x9y6z11-w6x6y7z11-w8x3y8z11-w10y9z11-wx14y3z12-
       -------------------------------------------------------------------------------------------
                                                                                                  
                                                                                                  
       w3x11y4z12-w5x8y5z12-w7x5y6z12-w9x2y7z12-x16yz13-w2x13y2z13-w4x10y3z13-w6x7y4z13-w8x4y5z13-
       -------------------------------------------------------------------------------------------
                                                                                            
                                                                                            
       w10xy6z13-wx15z14-w3x12yz14-w5x9y2z14-w7x6y3z14-w9x3y4z14-w11y5z14-w4x11z15-w6x8yz15-
       -------------------------------------------------------------------------------------------
                                                                       
                                                                       
       w8x5y2z15-w10x2y3z15-w7x7z16-w9x4yz16-w11xy2z16-w10x3z17-w12yz17
       -------------------------------------------------------------------------------------------
       -w8x10y10z2-w9x9y9z3-w10x8y8z4-w9x10y6z5-w10x9y5z6-w10x10y2z8                              
       -x17y10z3-wx16y9z4-w3x13y10z4-x18y7z5-w2x15y8z5-w4x12y9z5-w6x9y10z5-wx17y6z6-w3x14y7z6-w5x1
       x10y20+w2x7y21+wx9y19z+w3x6y20z+w5x3y21z+w2x8y18z2+w4x5y19z2+w6x2y20z2+wx10y16z3+w3x7y17z3+
       -------------------------------------------------------------------------------------------
                                                                                                  
       1y8z6-w7x8y9z6-w9x5y10z6-x19y4z7-w2x16y5z7-w4x13y6z7-w6x10y7z7-w8x7y8z7-w10x4y9z7-wx18y3z8-
       w5x4y18z3+w7xy19z3+w2x9y15z4+w4x6y16z4+w6x3y17z4+w8y18z4+w3x8y14z5+w5x5y15z5+w7x2y16z5+w2x1
       -------------------------------------------------------------------------------------------
                                                                                           
       w3x15y4z8-w5x12y5z8-w7x9y6z8-w9x6y7z8-x20yz9-w2x17y2z9-w4x14y3z9-w6x11y4z9-w8x8y5z9-
       0y12z6+w4x7y13z6+w6x4y14z6+w8xy15z6+wx12y10z7+w3x9y11z7+w5x6y12z7+w7x3y13z7+w9y14z7+
       -------------------------------------------------------------------------------------------
                                             
       w10x5y6z9-wx19z10-w3x16yz10-w5x13y2z10
       x14y8z8+w2x11y9z8+w4x8y10z8+w6x5y11z8+
       -------------------------------------------------------------------------------------------
                                                                                                  
       -w7x10y3z10-w9x7y4z10-w4x15z11-w6x12yz11-w8x9y2z11-w10x6y3z11-w7x11z12-w9x8yz12-w10x7z13   
       w8x2y12z8+wx13y7z9+w3x10y8z9+w5x7y9z9+w7x4y10z9+w9xy11z9+x15y5z10+w2x12y6z10+w4x9y7z10+w6x6
       -------------------------------------------------------------------------------------------
                                                                                             
                                                                                             
       y8z10+w8x3y9z10+w10y10z10+wx14y4z11+w3x11y5z11+w5x8y6z11+w7x5y7z11+w9x2y8z11+x16y2z12+
       -------------------------------------------------------------------------------------------
                                                                                                  
                                                                                                  
       w2x13y3z12+w4x10y4z12+w6x7y5z12+w8x4y6z12+w10xy7z12+wx15yz13+w3x12y2z13+w5x9y3z13+w7x6y4z13
       -------------------------------------------------------------------------------------------
                                                                                               
                                                                                               
       +w9x3y5z13+w11y6z13+w2x14z14+w4x11yz14+w6x8y2z14+w8x5y3z14+w10x2y4z14+w5x10z15+w7x7yz15+
       -------------------------------------------------------------------------------------------
                                                               |
                                                               |
       w9x4y2z15+w11xy3z15+w8x6z16+w10x3yz16+w12y2z16+w11x2z17 |

               3       3
o127 : Matrix R  <--- R

i128 :        

E3=generatingMorphism(I,3)
A=matrix entries relations E3#0
T=target A
U=matrix entries E3#1


              
o128 = (cokernel {-5} | z y x w |, 0)

o128 : Sequence

i129 : 
o129 = | z y x w |

               1       4
o129 : Matrix R  <--- R

i130 : 
        1
o130 = R

o130 : R-module, free

i131 : 
o131 = 0

               1       1
o131 : Matrix R  <--- R

i132 :               
E2=generatingMorphism(I,2)
A=matrix entries relations E2#0
T=target A
U=matrix entries E2#1

       
o132 = (cokernel {-3} | y  w  0 x 0 |, {-33} |
                 {-3} | -z -x y 0 w |  {-33} |
                 {-3} | 0  0  z y x |  {-33} |
       -------------------------------------------------------------------------------------------
       w9x8y10z3+w8x10y8z4+w10x7y9z4+w9x9y7z5+w10x8y6z6+w9x10y4z7+w10x9y3z8+w10x10z10             
       wx15y10z4+x17y8z5+w2x14y9z5+w4x11y10z5+wx16y7z6+w3x13y8z6+w5x10y9z6+w7x7y10z6+x18y5z7+w2x15
       -x9y21-wx8y20z-w3x5y21z-x10y18z2-w2x7y19z2-w4x4y20z2-w6xy21z2-wx9y17z3-w3x6y18z3-w5x3y19z3-
       -------------------------------------------------------------------------------------------
                                                                                                  
       y6z7+w4x12y7z7+w6x9y8z7+w8x6y9z7+w10x3y10z7+wx17y4z8+w3x14y5z8+w5x11y6z8+w7x8y7z8+w9x5y8z8+
       w7y20z3-w2x8y16z4-w4x5y17z4-w6x2y18z4-wx10y14z5-w3x7y15z5-w5x4y16z5-w7xy17z5-w2x9y13z6-w4x6
       -------------------------------------------------------------------------------------------
                                                                                                  
       x19y2z9+w2x16y3z9+w4x13y4z9+w6x10y5z9+w8x7y6z9+w10x4y7z9+wx18yz10+w3x15y2z10+w5x12y3z10+w7x
       y14z6-w6x3y15z6-w8y16z6-w3x8y12z7-w5x5y13z7-w7x2y14z7-x13y9z8-w2x10y10z8-w4x7y11z8-w6x4y12z
       -------------------------------------------------------------------------------------------
                                                                                              
       9y4z10+w9x6y5z10+w2x17z11+w4x14yz11+w6x11y2z11+w8x8y3z11+w10x5y4z11+w5x13z12+w7x10yz12+
       8-w8xy13z8-wx12y8z9-w3x9y9z9-w5x6y10z9-w7x3y11z9-w9y12z9-x14y6z10-w2x11y7z10-w4x8y8z10-
       -------------------------------------------------------------------------------------------
                                                                                                  
       w9x7y2z12+w8x9z13+w10x6yz13                                                                
       w6x5y9z10-w8x2y10z10-wx13y5z11-w3x10y6z11-w5x7y7z11-w7x4y8z11-w9xy9z11-x15y3z12-w2x12y4z12-
       -------------------------------------------------------------------------------------------
                                                                                                 
                                                                                                 
       w4x9y5z12-w6x6y6z12-w8x3y7z12-w10y8z12-wx14y2z13-w3x11y3z13-w5x8y4z13-w7x5y5z13-w9x2y6z13-
       -------------------------------------------------------------------------------------------
                                                                                             
                                                                                             
       x16z14-w2x13yz14-w4x10y2z14-w6x7y3z14-w8x4y4z14-w10xy5z14-w3x12z15-w5x9yz15-w7x6y2z15-
       -------------------------------------------------------------------------------------------
                                                                             
                                                                             
       w9x3y3z15-w11y4z15-w6x8z16-w8x5yz16-w10x2y2z16-w9x4z17-w11xyz17-w12z18
       -------------------------------------------------------------------------------------------
       w8x10y9z3+w10x7y10z3+w9x9y8z4+w10x8y7z5+w9x10y5z6+w10x9y4z7+w10x10yz9                      
       x17y9z4+w2x14y10z4+wx16y8z5+w3x13y9z5+w5x10y10z5+x18y6z6+w2x15y7z6+w4x12y8z6+w6x9y9z6+w8x6y
       -wx8y21-x10y19z-w2x7y20z-w4x4y21z-wx9y18z2-w3x6y19z2-w5x3y20z2-w7y21z2-w2x8y17z3-w4x5y18z3-
       -------------------------------------------------------------------------------------------
                                                                                      
       10z6+wx17y5z7+w3x14y6z7+w5x11y7z7+w7x8y8z7+w9x5y9z7+x19y3z8+w2x16y4z8+w4x13y5z8
       w6x2y19z3-wx10y15z4-w3x7y16z4-w5x4y17z4-w7xy18z4-w2x9y14z5-w4x6y15z5-w6x3y16z5-
       -------------------------------------------------------------------------------------------
                                                                                    
       +w6x10y6z8+w8x7y7z8+w10x4y8z8+wx18y2z9+w3x15y3z9+w5x12y4z9+w7x9y5z9+w9x6y6z9+
       w8y17z5-w3x8y13z6-w5x5y14z6-w7x2y15z6-x13y10z7-w2x10y11z7-w4x7y12z7-w6x4y13z7
       -------------------------------------------------------------------------------------------
                                                        
       x20z10+w2x17yz10+w4x14y2z10+w6x11y3z10+w8x8y4z10+
       -w8xy14z7-wx12y9z8-w3x9y10z8-w5x6y11z8-w7x3y12z8-
       -------------------------------------------------------------------------------------------
                                                                                                  
       w10x5y5z10+w3x16z11+w5x13yz11+w7x10y2z11+w9x7y3z11+w6x12z12+w8x9yz12+w10x6y2z12+w9x8z13    
       w9y13z8-x14y7z9-w2x11y8z9-w4x8y9z9-w6x5y10z9-w8x2y11z9-wx13y6z10-w3x10y7z10-w5x7y8z10-w7x4y
       -------------------------------------------------------------------------------------------
                                                                                           
                                                                                           
       9z10-w9xy10z10-x15y4z11-w2x12y5z11-w4x9y6z11-w6x6y7z11-w8x3y8z11-w10y9z11-wx14y3z12-
       -------------------------------------------------------------------------------------------
                                                                                                  
                                                                                                  
       w3x11y4z12-w5x8y5z12-w7x5y6z12-w9x2y7z12-x16yz13-w2x13y2z13-w4x10y3z13-w6x7y4z13-w8x4y5z13-
       -------------------------------------------------------------------------------------------
                                                                                            
                                                                                            
       w10xy6z13-wx15z14-w3x12yz14-w5x9y2z14-w7x6y3z14-w9x3y4z14-w11y5z14-w4x11z15-w6x8yz15-
       -------------------------------------------------------------------------------------------
                                                                       
                                                                       
       w8x5y2z15-w10x2y3z15-w7x7z16-w9x4yz16-w11xy2z16-w10x3z17-w12yz17
       -------------------------------------------------------------------------------------------
       -w8x10y10z2-w9x9y9z3-w10x8y8z4-w9x10y6z5-w10x9y5z6-w10x10y2z8                              
       -x17y10z3-wx16y9z4-w3x13y10z4-x18y7z5-w2x15y8z5-w4x12y9z5-w6x9y10z5-wx17y6z6-w3x14y7z6-w5x1
       x10y20+w2x7y21+wx9y19z+w3x6y20z+w5x3y21z+w2x8y18z2+w4x5y19z2+w6x2y20z2+wx10y16z3+w3x7y17z3+
       -------------------------------------------------------------------------------------------
                                                                                                  
       1y8z6-w7x8y9z6-w9x5y10z6-x19y4z7-w2x16y5z7-w4x13y6z7-w6x10y7z7-w8x7y8z7-w10x4y9z7-wx18y3z8-
       w5x4y18z3+w7xy19z3+w2x9y15z4+w4x6y16z4+w6x3y17z4+w8y18z4+w3x8y14z5+w5x5y15z5+w7x2y16z5+w2x1
       -------------------------------------------------------------------------------------------
                                                                                           
       w3x15y4z8-w5x12y5z8-w7x9y6z8-w9x6y7z8-x20yz9-w2x17y2z9-w4x14y3z9-w6x11y4z9-w8x8y5z9-
       0y12z6+w4x7y13z6+w6x4y14z6+w8xy15z6+wx12y10z7+w3x9y11z7+w5x6y12z7+w7x3y13z7+w9y14z7+
       -------------------------------------------------------------------------------------------
                                             
       w10x5y6z9-wx19z10-w3x16yz10-w5x13y2z10
       x14y8z8+w2x11y9z8+w4x8y10z8+w6x5y11z8+
       -------------------------------------------------------------------------------------------
                                                                                                  
       -w7x10y3z10-w9x7y4z10-w4x15z11-w6x12yz11-w8x9y2z11-w10x6y3z11-w7x11z12-w9x8yz12-w10x7z13   
       w8x2y12z8+wx13y7z9+w3x10y8z9+w5x7y9z9+w7x4y10z9+w9xy11z9+x15y5z10+w2x12y6z10+w4x9y7z10+w6x6
       -------------------------------------------------------------------------------------------
                                                                                             
                                                                                             
       y8z10+w8x3y9z10+w10y10z10+wx14y4z11+w3x11y5z11+w5x8y6z11+w7x5y7z11+w9x2y8z11+x16y2z12+
       -------------------------------------------------------------------------------------------
                                                                                                  
                                                                                                  
       w2x13y3z12+w4x10y4z12+w6x7y5z12+w8x4y6z12+w10xy7z12+wx15yz13+w3x12y2z13+w5x9y3z13+w7x6y4z13
       -------------------------------------------------------------------------------------------
                                                                                               
                                                                                               
       +w9x3y5z13+w11y6z13+w2x14z14+w4x11yz14+w6x8y2z14+w8x5y3z14+w10x2y4z14+w5x10z15+w7x7yz15+
       -------------------------------------------------------------------------------------------
                                                               |)
                                                               |
       w9x4y2z15+w11xy3z15+w8x6z16+w10x3yz16+w12y2z16+w11x2z17 |

o132 : Sequence

i133 : 
o133 = | y  w  0 x 0 |
       | -z -x y 0 w |
       | 0  0  z y x |

               3       5
o133 : Matrix R  <--- R

i134 : 
        3
o134 = R

o134 : R-module, free

i135 : 
o135 = | w9x8y10z3+w8x10y8z4+w10x7y9z4+w9x9y7z5+w10x8y6z6+w9x10y4z7+w10x9y3z8+w10x10z10           
       | wx15y10z4+x17y8z5+w2x14y9z5+w4x11y10z5+wx16y7z6+w3x13y8z6+w5x10y9z6+w7x7y10z6+x18y5z7+w2x
       | -x9y21-wx8y20z-w3x5y21z-x10y18z2-w2x7y19z2-w4x4y20z2-w6xy21z2-wx9y17z3-w3x6y18z3-w5x3y19z
       -------------------------------------------------------------------------------------------
                                                                                                  
       15y6z7+w4x12y7z7+w6x9y8z7+w8x6y9z7+w10x3y10z7+wx17y4z8+w3x14y5z8+w5x11y6z8+w7x8y7z8+w9x5y8z
       3-w7y20z3-w2x8y16z4-w4x5y17z4-w6x2y18z4-wx10y14z5-w3x7y15z5-w5x4y16z5-w7xy17z5-w2x9y13z6-w4
       -------------------------------------------------------------------------------------------
                                                                                                  
       8+x19y2z9+w2x16y3z9+w4x13y4z9+w6x10y5z9+w8x7y6z9+w10x4y7z9+wx18yz10+w3x15y2z10+w5x12y3z10+w
       x6y14z6-w6x3y15z6-w8y16z6-w3x8y12z7-w5x5y13z7-w7x2y14z7-x13y9z8-w2x10y10z8-w4x7y11z8-w6x4y1
       -------------------------------------------------------------------------------------------
                                                                                                
       7x9y4z10+w9x6y5z10+w2x17z11+w4x14yz11+w6x11y2z11+w8x8y3z11+w10x5y4z11+w5x13z12+w7x10yz12+
       2z8-w8xy13z8-wx12y8z9-w3x9y9z9-w5x6y10z9-w7x3y11z9-w9y12z9-x14y6z10-w2x11y7z10-w4x8y8z10-
       -------------------------------------------------------------------------------------------
                                                                                                  
       w9x7y2z12+w8x9z13+w10x6yz13                                                                
       w6x5y9z10-w8x2y10z10-wx13y5z11-w3x10y6z11-w5x7y7z11-w7x4y8z11-w9xy9z11-x15y3z12-w2x12y4z12-
       -------------------------------------------------------------------------------------------
                                                                                                 
                                                                                                 
       w4x9y5z12-w6x6y6z12-w8x3y7z12-w10y8z12-wx14y2z13-w3x11y3z13-w5x8y4z13-w7x5y5z13-w9x2y6z13-
       -------------------------------------------------------------------------------------------
                                                                                             
                                                                                             
       x16z14-w2x13yz14-w4x10y2z14-w6x7y3z14-w8x4y4z14-w10xy5z14-w3x12z15-w5x9yz15-w7x6y2z15-
       -------------------------------------------------------------------------------------------
                                                                             
                                                                             
       w9x3y3z15-w11y4z15-w6x8z16-w8x5yz16-w10x2y2z16-w9x4z17-w11xyz17-w12z18
       -------------------------------------------------------------------------------------------
       w8x10y9z3+w10x7y10z3+w9x9y8z4+w10x8y7z5+w9x10y5z6+w10x9y4z7+w10x10yz9                      
       x17y9z4+w2x14y10z4+wx16y8z5+w3x13y9z5+w5x10y10z5+x18y6z6+w2x15y7z6+w4x12y8z6+w6x9y9z6+w8x6y
       -wx8y21-x10y19z-w2x7y20z-w4x4y21z-wx9y18z2-w3x6y19z2-w5x3y20z2-w7y21z2-w2x8y17z3-w4x5y18z3-
       -------------------------------------------------------------------------------------------
                                                                                      
       10z6+wx17y5z7+w3x14y6z7+w5x11y7z7+w7x8y8z7+w9x5y9z7+x19y3z8+w2x16y4z8+w4x13y5z8
       w6x2y19z3-wx10y15z4-w3x7y16z4-w5x4y17z4-w7xy18z4-w2x9y14z5-w4x6y15z5-w6x3y16z5-
       -------------------------------------------------------------------------------------------
                                                                                    
       +w6x10y6z8+w8x7y7z8+w10x4y8z8+wx18y2z9+w3x15y3z9+w5x12y4z9+w7x9y5z9+w9x6y6z9+
       w8y17z5-w3x8y13z6-w5x5y14z6-w7x2y15z6-x13y10z7-w2x10y11z7-w4x7y12z7-w6x4y13z7
       -------------------------------------------------------------------------------------------
                                                        
       x20z10+w2x17yz10+w4x14y2z10+w6x11y3z10+w8x8y4z10+
       -w8xy14z7-wx12y9z8-w3x9y10z8-w5x6y11z8-w7x3y12z8-
       -------------------------------------------------------------------------------------------
                                                                                                  
       w10x5y5z10+w3x16z11+w5x13yz11+w7x10y2z11+w9x7y3z11+w6x12z12+w8x9yz12+w10x6y2z12+w9x8z13    
       w9y13z8-x14y7z9-w2x11y8z9-w4x8y9z9-w6x5y10z9-w8x2y11z9-wx13y6z10-w3x10y7z10-w5x7y8z10-w7x4y
       -------------------------------------------------------------------------------------------
                                                                                           
                                                                                           
       9z10-w9xy10z10-x15y4z11-w2x12y5z11-w4x9y6z11-w6x6y7z11-w8x3y8z11-w10y9z11-wx14y3z12-
       -------------------------------------------------------------------------------------------
                                                                                                  
                                                                                                  
       w3x11y4z12-w5x8y5z12-w7x5y6z12-w9x2y7z12-x16yz13-w2x13y2z13-w4x10y3z13-w6x7y4z13-w8x4y5z13-
       -------------------------------------------------------------------------------------------
                                                                                            
                                                                                            
       w10xy6z13-wx15z14-w3x12yz14-w5x9y2z14-w7x6y3z14-w9x3y4z14-w11y5z14-w4x11z15-w6x8yz15-
       -------------------------------------------------------------------------------------------
                                                                       
                                                                       
       w8x5y2z15-w10x2y3z15-w7x7z16-w9x4yz16-w11xy2z16-w10x3z17-w12yz17
       -------------------------------------------------------------------------------------------
       -w8x10y10z2-w9x9y9z3-w10x8y8z4-w9x10y6z5-w10x9y5z6-w10x10y2z8                              
       -x17y10z3-wx16y9z4-w3x13y10z4-x18y7z5-w2x15y8z5-w4x12y9z5-w6x9y10z5-wx17y6z6-w3x14y7z6-w5x1
       x10y20+w2x7y21+wx9y19z+w3x6y20z+w5x3y21z+w2x8y18z2+w4x5y19z2+w6x2y20z2+wx10y16z3+w3x7y17z3+
       -------------------------------------------------------------------------------------------
                                                                                                  
       1y8z6-w7x8y9z6-w9x5y10z6-x19y4z7-w2x16y5z7-w4x13y6z7-w6x10y7z7-w8x7y8z7-w10x4y9z7-wx18y3z8-
       w5x4y18z3+w7xy19z3+w2x9y15z4+w4x6y16z4+w6x3y17z4+w8y18z4+w3x8y14z5+w5x5y15z5+w7x2y16z5+w2x1
       -------------------------------------------------------------------------------------------
                                                                                           
       w3x15y4z8-w5x12y5z8-w7x9y6z8-w9x6y7z8-x20yz9-w2x17y2z9-w4x14y3z9-w6x11y4z9-w8x8y5z9-
       0y12z6+w4x7y13z6+w6x4y14z6+w8xy15z6+wx12y10z7+w3x9y11z7+w5x6y12z7+w7x3y13z7+w9y14z7+
       -------------------------------------------------------------------------------------------
                                             
       w10x5y6z9-wx19z10-w3x16yz10-w5x13y2z10
       x14y8z8+w2x11y9z8+w4x8y10z8+w6x5y11z8+
       -------------------------------------------------------------------------------------------
                                                                                                  
       -w7x10y3z10-w9x7y4z10-w4x15z11-w6x12yz11-w8x9y2z11-w10x6y3z11-w7x11z12-w9x8yz12-w10x7z13   
       w8x2y12z8+wx13y7z9+w3x10y8z9+w5x7y9z9+w7x4y10z9+w9xy11z9+x15y5z10+w2x12y6z10+w4x9y7z10+w6x6
       -------------------------------------------------------------------------------------------
                                                                                             
                                                                                             
       y8z10+w8x3y9z10+w10y10z10+wx14y4z11+w3x11y5z11+w5x8y6z11+w7x5y7z11+w9x2y8z11+x16y2z12+
       -------------------------------------------------------------------------------------------
                                                                                                  
                                                                                                  
       w2x13y3z12+w4x10y4z12+w6x7y5z12+w8x4y6z12+w10xy7z12+wx15yz13+w3x12y2z13+w5x9y3z13+w7x6y4z13
       -------------------------------------------------------------------------------------------
                                                                                               
                                                                                               
       +w9x3y5z13+w11y6z13+w2x14z14+w4x11yz14+w6x8y2z14+w8x5y3z14+w10x2y4z14+w5x10z15+w7x7yz15+
       -------------------------------------------------------------------------------------------
                                                               |
                                                               |
       w9x4y2z15+w11xy3z15+w8x6z16+w10x3yz16+w12y2z16+w11x2z17 |

               3       3
o135 : Matrix R  <--- R

i136 :        p=2; --- p=2 behaves differently!
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


for k from 0 to 4 do
    print (k, prune Ext^k(coker I, R^1));

time LT=LyubeznikTable(I)
peek(LT) -- only l(2,2)=1

E0=generatingMorphism(I,0)
E1=generatingMorphism(I,1)
E2=generatingMorphism(I,2)
E3=generatingMorphism(I,3)
E4=generatingMorphism(I,4)


E2=generatingMorphism(I,2)
A=matrix entries relations E2#0
T=target A
U=matrix entries E2#1


i137 : 
i138 :        
o138 : Ideal of R

i139 : 
               1       4
o139 : Matrix R  <--- R

i140 : 
i141 : 
o141 = ChainComplex{cache => CacheTable{}                                   }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy+wz x3+w2y wy2+x2z y3+xz2 |

                               4                           4
                          1 : R  <----------------------- R  : 2
                                    {2} | x2 wy xz y2 |
                                    {3} | y  z  0  0  |
                                    {3} | w  x  y  z  |
                                    {3} | 0  0  w  x  |

                               4                 1
                          2 : R  <------------- R  : 3
                                    {4} | z |
                                    {4} | y |
                                    {4} | x |
                                    {4} | w |

                               1
                          3 : R  <----- 0 : 4
                                    0

i142 :      -- used 0.174684 seconds

o142 = MutableHashTable{...1...}

o142 : MutableHashTable

i143 : 
o143 = MutableHashTable{(2, 2) => 1}

i144 :                      (0, 0)
(1, 0)
(2, cokernel {-3} | y w 0 x 0 |)
             {-3} | z x y 0 w |
             {-3} | 0 0 z y x |
(3, cokernel {-5} | z y x w |)
(4, 0)

i145 :             -- used 0.169221 seconds

o145 = MutableHashTable{...1...}

o145 : MutableHashTable

i146 : 
o146 = MutableHashTable{(2, 2) => 1}

i147 :        
o147 = (image 0, 0)

o147 : Sequence

i148 : 
o148 = (0, 0)

o148 : Sequence

i149 : 
o149 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o149 : Sequence

i150 : 
o150 = (cokernel {-5} | z y x w |, 0)

o150 : Sequence

i151 : 
o151 = (0, 0)

o151 : Sequence

i152 :               
o152 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o152 : Sequence

i153 : 
o153 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o153 : Matrix R  <--- R

i154 : 
        3
o154 = R

o154 : R-module, free

i155 : 
o155 = | wxz    wxy     0       |
       | wyz    x2z     x2y+wxz |
       | y3+xz2 xyz+wz2 xy2+wyz |

               3       3
o155 : Matrix R  <--- R

i156 :        U

o156 = | wxz    wxy     0       |
       | wyz    x2z     x2y+wxz |
       | y3+xz2 xyz+wz2 xy2+wyz |

               3       3
o156 : Matrix R  <--- R

i157 : 
E3=generatingMorphism(I,3)
A=matrix entries relations E3#0
T=target A
U=matrix entries E3#1


       
o157 = (cokernel {-5} | z y x w |, 0)

o157 : Sequence

i158 : 
o158 = | z y x w |

               1       4
o158 : Matrix R  <--- R

i159 : 
        1
o159 = R

o159 : R-module, free

i160 : 
o160 = 0

               1       1
o160 : Matrix R  <--- R

i161 :      U              U         

o161 = 0

               1       1
o161 : Matrix R  <--- R

i162 : A

o162 = | z y x w |

               1       4
o162 : Matrix R  <--- R

i163 : U

o163 = 0

               1       1
o163 : Matrix R  <--- R

i164 : E2=generatingMorphism(I,2)
A=matrix entries relations E2#0
T=target A
U=matrix entries E2#1


o164 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o164 : Sequence

i165 : 
o165 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o165 : Matrix R  <--- R

i166 : 
        3
o166 = R

o166 : R-module, free

i167 : 
o167 = | wxz    wxy     0       |
       | wyz    x2z     x2y+wxz |
       | y3+xz2 xyz+wz2 xy2+wyz |

               3       3
o167 : Matrix R  <--- R

i168 :        generatingRoot (A,U)


o168 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o168 : Matrix R  <--- R

i169 : A       A       

o169 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o169 : Matrix R  <--- R

i170 : A

o170 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o170 : Matrix R  <--- R

i171 :     L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;


o171 : Ideal of R

i172 : 
o172 : Ideal of R

i173 : 
i174 : 
i175 : 
i176 : stdio:566:22:(3): error: expected objects in the same ring

i177 :        p=2; --- p=2 behaves differently!
R=ZZ/p[w,x,y,z];
--R=QQ[w,x,y,z];
I=ideal(x*y-w*z, y^3-x*z^2, w*y^2-x^2*z, x^3-w^2*y);
I=gens I;
www=res coker I;
peek(www)
time LT=LyubeznikTable(I)
peek(LT)


for k from 0 to 4 do
    print (k, prune Ext^k(coker I, R^1));

time LT=LyubeznikTable(I)
peek(LT) -- only l(2,2)=1

E0=generatingMorphism(I,0)
E1=generatingMorphism(I,1)
E2=generatingMorphism(I,2)
E3=generatingMorphism(I,3)
E4=generatingMorphism(I,4)


E2=generatingMorphism(I,2)
A=matrix entries relations E2#0
T=target A
U=matrix entries E2#1

generatingRoot (A,U)

---F=MfilterSequence(A,3)
F={w,z,w};
------------------------------------
i=0

---    F=MfilterSequence(A,1);
    L0=ideal(0_R);
    L1=ideal(0_R);
    f=1_R;
    g=F#0;
    h=0_R;
    B=(L1*T+image(A)):g;


i178 : 
i179 :        
o179 : Ideal of R

i180 : 
               1       4
o180 : Matrix R  <--- R

i181 : 
i182 : 
o182 = ChainComplex{cache => CacheTable{}                                   }
                    Resolution => Resolution{...8...}
                    ring => R
                               1                                       4
                    dd => 0 : R  <----------------------------------- R  : 1
                                    | xy+wz x3+w2y wy2+x2z y3+xz2 |

                               4                           4
                          1 : R  <----------------------- R  : 2
                                    {2} | x2 wy xz y2 |
                                    {3} | y  z  0  0  |
                                    {3} | w  x  y  z  |
                                    {3} | 0  0  w  x  |

                               4                 1
                          2 : R  <------------- R  : 3
                                    {4} | z |
                                    {4} | y |
                                    {4} | x |
                                    {4} | w |

                               1
                          3 : R  <----- 0 : 4
                                    0

i183 :      -- used 0.184186 seconds

o183 = MutableHashTable{...1...}

o183 : MutableHashTable

i184 : 
o184 = MutableHashTable{(2, 2) => 1}

i185 :                      (0, 0)
(1, 0)
(2, cokernel {-3} | y w 0 x 0 |)
             {-3} | z x y 0 w |
             {-3} | 0 0 z y x |
(3, cokernel {-5} | z y x w |)
(4, 0)

i186 :             -- used 0.171448 seconds

o186 = MutableHashTable{...1...}

o186 : MutableHashTable

i187 : 
o187 = MutableHashTable{(2, 2) => 1}

i188 :        
o188 = (image 0, 0)

o188 : Sequence

i189 : 
o189 = (0, 0)

o189 : Sequence

i190 : 
o190 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o190 : Sequence

i191 : 
o191 = (cokernel {-5} | z y x w |, 0)

o191 : Sequence

i192 : 
o192 = (0, 0)

o192 : Sequence

i193 :               
o193 = (cokernel {-3} | y w 0 x 0 |, {-6} | wxz    wxy     0       |)
                 {-3} | z x y 0 w |  {-6} | wyz    x2z     x2y+wxz |
                 {-3} | 0 0 z y x |  {-6} | y3+xz2 xyz+wz2 xy2+wyz |

o193 : Sequence

i194 : 
o194 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o194 : Matrix R  <--- R

i195 : 
        3
o195 = R

o195 : R-module, free

i196 : 
o196 = | wxz    wxy     0       |
       | wyz    x2z     x2y+wxz |
       | y3+xz2 xyz+wz2 xy2+wyz |

               3       3
o196 : Matrix R  <--- R

i197 :        
o197 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o197 : Matrix R  <--- R

i198 :               
i199 :        
o199 = 0

i200 :               
o200 : Ideal of R

i201 : 
o201 : Ideal of R

i202 : 
i203 : 
i204 : 
i205 : 
i206 :        B

o206 = image | y w 0 x 0 |
             | z x y 0 w |
             | 0 0 z y x |

                               3
o206 : R-module, submodule of R

i207 : A

o207 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o207 : Matrix R  <--- R

i208 :     C=L0*T+h*T+image(A);


i209 :        C

o209 = image | 0 0 0 0 0 0 y w 0 x 0 |
             | 0 0 0 0 0 0 z x y 0 w |
             | 0 0 0 0 0 0 0 0 z y x |

                               3
o209 : R-module, submodule of R

i210 : mingens image A

o210 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o210 : Matrix R  <--- R

i211 : 

i=1;
---    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);

              
i212 :        
o212 : Ideal of R

i213 : 
o213 : Ideal of R

i214 :        L0

o214 = ideal 0

o214 : Ideal of R

i215 : L1

o215 = ideal w

o215 : Ideal of R

i216 :     f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);


i217 : 
i218 : 
i219 :       g       g 

o219 = z

o219 : R

i220 :     B=(L1*T+image(A)):g;


i221 :    B       B    

o221 = image | w y 0 0 0 x 0 0 |
             | 0 z x w y 0 0 0 |
             | 0 0 0 0 z y x w |

                               3
o221 : R-module, submodule of R

i222 : A

o222 = | y w 0 x 0 |
       | z x y 0 w |
       | 0 0 z y x |

               3       5
o222 : Matrix R  <--- R

i223 : mingens B

o223 = | w y 0 0 0 x 0 0 |
       | 0 z x w y 0 0 0 |
       | 0 0 0 0 z y x w |

               3       8
o223 : Matrix R  <--- R

i224 :     C=L0*T+h*T+image(A);


i225 :        C

o225 = image | 0 0 0 w 0 0 y w 0 x 0 |
             | 0 0 0 0 w 0 z x y 0 w |
             | 0 0 0 0 0 w 0 0 z y x |

                               3
o225 : R-module, submodule of R

i226 : mingens C

o226 = | w y 0 0 0 x 0 0 |
       | 0 z x w y 0 0 0 |
       | 0 0 0 0 z y x w |

               3       8
o226 : Matrix R  <--- R

i227 :     L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);


o227 : Ideal of R

i228 : 
o228 : Ideal of R

i229 :   L0       L0     

o229 = ideal 0

o229 : Ideal of R

i230 : 
i=2;
---    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);

       
i231 :        
o231 : Ideal of R

i232 : 
o232 : Ideal of R

i233 :        L0

o233 = ideal w

o233 : Ideal of R

i234 : L1

o234 = ideal 1

o234 : Ideal of R

i235 :     f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;


i236 : 
i237 : 
i238 : 
i239 :   B       B     

        3
o239 = R

o239 : R-module, free

i240 : g

o240 = w

o240 : R

i241 :     V=f*U;
    C=L0*T+h*T+image(A);


               3       3
o241 : Matrix R  <--- R

i242 : 
i243 :     C       C   

o243 = image | w 0 0 z 0 0 y w 0 x 0 |
             | 0 w 0 0 z 0 z x y 0 w |
             | 0 0 w 0 0 z 0 0 z y x |

                               3
o243 : R-module, submodule of R

i244 : mingens C

o244 = | z y w 0 0 0 0 0 x 0 0 |
       | 0 0 0 z y x w 0 0 0 0 |
       | 0 0 0 0 0 0 0 z y x w |

               3       11
o244 : Matrix R  <--- R

i245 : 

i=2;
---    F=MfilterSequence(A,i+1);
    L0=lowLimClosure(F,i);
    L1=lowLimClosure(F,i+1);
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g;
    V=f*U;
    C=L0*T+h*T+image(A);
 
              
i246 :        
o246 : Ideal of R

i247 : 
o247 : Ideal of R

i248 : 
i249 : 
i250 : 
i251 : 
i252 : 
               3       3
o252 : Matrix R  <--- R

i253 : 
i254 :           (X,Y,W)=generatingSubquotientRoot (gens B,gens C,V);
 

i255 :        X

o255 = | 1 0 0 |
       | 0 1 0 |
       | 0 0 1 |

               3       3
o255 : Matrix R  <--- R

i256 : B

        3
o256 = R

o256 : R-module, free

i257 : C

o257 = image | w 0 0 z 0 0 y w 0 x 0 |
             | 0 w 0 0 z 0 z x y 0 w |
             | 0 0 w 0 0 z 0 0 z y x |

                               3
o257 : R-module, submodule of R

i258 : Y

o258 = | 0 z y w 0 x 0 0 |
       | 1 0 0 0 0 0 0 0 |
       | 0 0 0 0 z y x w |

               3       8
o258 : Matrix R  <--- R

i259 : W

o259 = cokernel | z y w 0 x 0 0 |
                | 0 0 0 z y x w |

                              2
o259 : R-module, quotient of R

i260 : X

o260 = | 1 0 0 |
       | 0 1 0 |
       | 0 0 1 |

               3       3
o260 : Matrix R  <--- R

i261 :      	    G1=Hom(coker vars(R),  W); 
    	    answer=rank source mingens G1;   


i262 : 
i263 :        G1

o263 = subquotient (| x |, | z y w 0 x 0 0 |)
                    | 0 |  | 0 0 0 z y x w |

                                 2
o263 : R-module, subquotient of R

i264 : answer

o264 = 1

i265 : 