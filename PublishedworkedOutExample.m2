
 restart;


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



--- Detailed calculation based on the Example  in 
--- J. ALVAREZ MONTANER Characteristic cycles of local cohomology modules of monomial ideals, page 23
p=2
R=ZZ/p[x_1..x_7];
I=interseect(ideal(x_1, x_2), ideal(x_3, x_4), ideal(x_5, x_6, x_7));
I=gens I;
time LT=LyubeznikTable(I)
peek(LT)



--- We now recreate the details of the calculations in section 6 of "Lyubeznik numbers, F-modules and modules of generalized fractions"

--- Here is a filter sequence on Coker A
F= {x_1+x_2+x_4+x_5+x_7, x_2+x_3+x_4+x_5+x_6+x_7, x_3+x_6+x_7, x_2, x_1}


--- Compute a generating morphism for H^{n-j}_I(R)
n=7;
j=4;
E=generatingMorphism(I,n-j)
U=matrix entries (E#1)
A=relations E#0; A=matrix entries A
T=target(A);
G=generatingRoot(A,U)



--- Compute the (3,4) Lyubeznik number
i=3;

    L0=lowLimClosure(F,i)
    L1=lowLimClosure(F,i+1)
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g
    V=f*U;
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

G1=prune subquotient(gens B,C1);
<< "The (3,4) Lyubeznik Number is " <<rank ambient G1 << "\n";




--- Compute the (4,4) Lyubeznik number
i=4;

    L0=lowLimClosure(F,i)
    L1=lowLimClosure(F,i+1)
    f=product toList apply(0..(i-1), t->(F#t)^(p-1));
    g=F#i;
    h=F#(i-1);
    B=(L1*T+image(A)):g
    V=f*U;
    C=L0*T+h*T+image(A)

	C0=gens C;
	Bp=frobeniusPowerX(gens B,1);
	Cp=frobeniusPowerX(C0,1);
	assert ((V*(gens B))%(Bp)==0);
	assert ((V*C0)%(Cp)==0);
	C1= matrixColon(Cp, V);
	C1=matrix entries C1;
	C1= gens (intersect(image(C1), B));
	print ((C1%C0)==0);  -- C1<>C0 so we havent yet stabilized
	
    	C0=C1;
   	Cp=frobeniusPowerX(C0,1);
	C1= matrixColon(Cp, V);
	C1=matrix entries C1;
	C1= gens (intersect(image(C1), B));
	print ((C1%C0)==0);


G1=prune subquotient(gens B,C1);
<< "The (4,4) Lyubeznik Number is " <<rank ambient G1 << "\n";






------------------------------------------------------------------------------------------------------------------------------------------


--- Example 4.8 in 
--- J. ALVAREZ MONTANER AND A. VAHIDI: Lyubeznik numbers of monomial ideals, Trans. Amer. Math. Soc. 366 (2014), no. 4, 1829–1855.
p=2
R=ZZ/p[x_1..x_6];
I=ideal(x_1*x_2*x_3, x_1*x_2*x_4, x_1*x_3*x_5, x_1*x_4*x_6, x_1*x_5*x_6, 
    x_2*x_3*x_6, x_2*x_4*x_5, x_2*x_5*x_6, x_3*x_4*x_5, x_3*x_4*x_6);
I=gens I;
time LT=LyubeznikTable(I)
peek(LT)
------------------------------------------------------------------------------------------------------------------------------------------


--- Example 5.3 in 
--- J. ALVAREZ MONTANER AND A. VAHIDI: Lyubeznik numbers of monomial ideals, Trans. Amer. Math. Soc. 366 (2014), no. 4, 1829–1855.
p=2
R=ZZ/p[x_1..x_5];
I=intersect(ideal(x_1, x_2, x_5), ideal (x_3, x_4, x_5), ideal(x_1, x_2, x_3, x_4))
I=gens I;
time LT=LyubeznikTable(I)
peek(LT)

------------------------------------------------------------------------------------------------------------------------------------------

