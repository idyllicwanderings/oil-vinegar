// Project 2
// Created by Maltose
// 26/04/2022

clear;

//++++++++++++++++++++++++++++++++++++++++++ Task 1 +++++++++++++++++++++++++++++++++++++++++++++++
// Task 1a
// input : OVKeyGen(Fq::FldFin, n::RngIntElt, v::RngIntElt)
// outpt : -> F::SeqEnum, T::AlgMatElt, P::SeqEnum
// TODO: 我们需要保持这个是对称的吗。

function OVKeyGen(Fq,n,v)

    q := Characteristic(Fq);
    m := n - v;
    //R<[x]> := PolynomialRing(Fq,n) ;
    // poly := [];
    // for i in [1..#x] do
    //     poly := Append(poly,x[i]^q+x[i]);
    // end for;
    Q<[x]> := PolynomialRing(Fq,n); //quotient rings of R

    // linear map T ====================================================================== 
    T := ZeroMatrix(Fq,n,n);
    repeat
        T := Random(GL(n,Fq));
    until Determinant(T) ne 0;
    
    // central map F=======================================================================
    // Assuming F is symmetric.
    // v,n : αi,j,kxixj

    F_matrix := [];
    F := [];
    for i in [1..m] do 
        F_matrix[i] := ZeroMatrix(Fq,n,n);
        cur_poly := Q ! 0;
        
        for j in [1..v] do // diagnoal
            for k in [j..v] do 
                a := Random(Fq);
                b := 0;
                if j eq k then
                    cur_poly +:= a * x[j]* x[k];
                    F_matrix[i][j][k] := a;
                else
                    cur_poly +:= (a + b) * x[j]* x[k];
	                F_matrix[i][j][k] := a;
                    //F_matrix[i][k][j] := b;
                end if;
            end for;
        end for;

        for j in [1..m] do
            for k in [1..v] do
                a := Random(Fq); 
                b := 0;
                cur_poly +:= (a+b) * x[k] * x[v+j];
                //F_matrix[i][j+v][k] := a;
                F_matrix[i][k][j+v] := a;
            end for;
        end for;
 
        F[i] := cur_poly;

    end for;

    // create P =======================================================================


    P_matrix := [];  // create the matrix T^tFT
    for i in [1..m] do
        P_matrix[i] := Transpose(T) * F_matrix[i] * T;
    end for;

    P := [];   // transfer matrix to the public key
    for k in [1..m] do
        tmp := ZeroMatrix(Q,n,1);
        for i in [1..n] do 
            for j in [1..n] do //generate first x_j
                tmp[i][1] +:= P_matrix[k][i][j] * x[j] *x[i];
            end for;
        end for;
        tmp1 := Q ! 0;
        for i in [1..n] do  //..no generate second x_i 
            tmp1 +:= tmp[i][1] ;
        end for;
        P[k] := tmp1;
    end for;

    return F,T,P;

end function;


//++++++++++++++++++++++++++++++++++++++++++ Task 1b +++++++++++++++++++++++++++++++++++++++++++++++
//Task 1b
// (h::SeqEnum, F::SeqEnum, T::AlgMatElt) -> sgn::SeqEnum

function OVSign(h,F,T)

    m := #F;
    n := Nrows(T);
    v := n - m;

    Fq := Parent(T[1][1]);
    q := Characteristic(Fq);
    R<[x]> := PolynomialRing(Fq,n);
    //Pol<[y]>:=PolynomialRing(Fq,n);

    var := [];


    repeat
        var := [Random(Fq): i in [1..v]] cat [x[i+v]:i in [1..m]]; //find v random values
        x_0 := [Fq!0: i in [1..n]];

	    poly_oil := [Evaluate(F[i],var): i in [1..m]]; // solution of values of x[v+1]..x[n]
        cons := [Evaluate(poly_oil[i],x_0): i in [1..m]]; // constant terms

	    V := ZeroMatrix(Fq,m,m); // Vx = y
	    for i in [1..m] do
	        for j in [1..m] do
                // print("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx");
                // print(Coefficient(poly_oil[i],x[j+v],1));
                // print("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx");
	            V[j][i] := Fq! Coefficient(poly_oil[i],x[j+v],1); //x_v+1,..,x_n
	        end for;
	    end for;

        //print("no solution!");

    until Rank(V) eq m;

    // calculting X = V-1 * h
    // HIGHLIGHT: 别忘了减去常数项！！！！！！气死我了！！！！
    Y := [h[i]-cons[i]:i in[1..m]];
    sol_m :=  ElementToSequence(Vector(Fq,Y) * V^-1);
    sol_n := [var[i]: i in [1..v]] cat [sol_m[i]: i in [1..m]];

    //calculating T^-1(X) = T^-1 * X = (X^T * (T^-1)^t)T, suppose X is a column vector!!!!!!
    sgn := ElementToSequence(Vector(Fq,sol_n) * Transpose(T^-1));
    return sgn;

end function;


//++++++++++++++++++++++++++++++++++++++++++ Task 1c +++++++++++++++++++++++++++++++++++++++++++++++
//Task 1c
//Verify(h::SeqEnum, P::SeqEnum, sgn::SeqEnum) -> vf:BoolElt
function Verify(h,P,sgn)

    m := #P;
    P_z := [Evaluate(P[i],sgn): i in [1..m]];
    vf := h eq P_z;
    print("P_z is"); P_z;
    return vf;

end function;



// Test of Task 1 

// Fq := FiniteField(31);
// n := 22;
// v := 11;
// h := [23,15,2,18,19,0,11,26,30,14,3];
// F,T,P := OVKeyGen(Fq,n,v);
// sgn := OVSign(h,F,T);
// print("h is"); h;
// Verify(h,P,sgn);








//++++++++++++++++++++++++++++++++++++++++++ Task 2a +++++++++++++++++++++++++++++++++++++++++++++++
// n := 128;
// v := 64;
// // n := 192;
// // v := 128;
// Fq := FiniteField(2^16);
// h := [Random(Fq): i in [1..n-v]];
// F,T,P := OVKeyGen(Fq,n,v);
// sgn := OVSign(h,F,T);
// Verify(h,P,sgn);
// #Sprint(F);
// #Sprint(T);
// #Sprint(P);
// #Sprint(sgn);




//++++++++++++++++++++++++++++++++++++++++++ Task 2b +++++++++++++++++++++++++++++++++++++++++++++++
procedure Task2b()
    n := 60;
    v := 1;
    Fq := FiniteField(2^2);
    h := [Random(Fq): i in [1..n-v]];
    F,T,P := OVKeyGen(Fq,n,v);
    sgn := OVSign(h,F,T);

end procedure;

//Task2b();


//++++++++++++++++++++++++++++++++++++++++++ Task 3a +++++++++++++++++++++++++++++++++++++++++++++++


function GuessAttack(P,h)
    // Define fields and rings
    PR<[x]> := Parent(P[1]); 
    Fq := BaseRing(PR); //finite field F_q
    q := Characteristic(Fq);
    
    n := Rank(PR); 
    m := #P;       
    v := n - m; // Assuming we have m = v = n/2 and n is even.

    k := 10;
    repeat
        var := [Random(Fq): i in [1..v+k]] cat  [x[i+k+v]:i in [1..m-k]];
        poly_oil := [Evaluate(P[i],var): i in [1..m]];
        poly_oil := [poly_oil[i] - h[i]: i in [1..m]];


        // add field equations
        for k in [1..m] do
            poly_oil := poly_oil cat [x[k]^(q) - x[k]];
        end for;


        poly_oil := ChangeUniverse(poly_oil,PR);



        I := Ideal(poly_oil); //TODO: base ring
        basis := GroebnerBasis(I);

        //print(basis);

    until #basis ge 2;
    
    //print("basis is"); basis;

    sgn := [];

    for i in [m-k..2 by -1] do
        root := Roots(UnivariatePolynomial(basis[i]))[1][1];
        sgn := Append(sgn, root);
        for j in [i-1..1 by -1] do
            basis[j] := Evaluate(basis[j],x[i],root);
        end for;
    end for;

    sgn := Append(sgn,Roots(UnivariatePolynomial(basis[1]))[1][1]);

    sgn := var[1..v+k] cat Reverse(sgn);

    return sgn;

end function;





procedure Task3a()
    // test of task 3
    Fq := FiniteField(3);
    n := 60;
    v := 40;
    h := [0, 5, 2, 1,3,1,2,8,9,0,1,2,0,1,3,1,2,3,0,0];

    // n := 8;
    // v := 4;
    // h := [23,15,2,18];

    F,T,P := OVKeyGen(Fq,n,v);
    print("[task3] h is"); h;
    start_time := Realtime();
    sgn := GuessAttack(P,h);
    end_time := Realtime();
    rt := (end_time - start_time); 
    print("running time is"); rt/60;


end procedure;

//Task3a();



//++++++++++++++++++++++++++++++++++++++++++ Task 6 +++++++++++++++++++++++++++++++++++++++++++++++

// KSAttack(P::SeqEnum) -> T::AlgMatElt

function KSAttack(P)

    // Define fields and rings
    PR<[x]> := Parent(P[1]); // ring
    Fq := BaseRing(PR); //finite field F_q
    
    n := Rank(PR); 
    q := Characteristic(Fq);
    m := #P;       
    v := n - m; // Assuming we have m = v = n/2 and n is even.

    G := [];

    for l in [1..m] do // recover the matrix of P
        M_tmp := [];
        for i in [1..n] do
            E := [];
            for j in [1..n] do
                if i ne j then
                    // E := Append(E,(2^-1)*MonomialCoefficient(P[l],x[i]*x[j])); //TODO: 这个1/2有必要么。
                    E := Append(E, MonomialCoefficient(P[l],x[i]*x[j]));
                else
                    // E := Append(E, MonomialCoefficient(P[l],x[i]*x[j]));
                    E := Append(E, MonomialCoefficient(P[l],x[i]*x[j]) + MonomialCoefficient(P[l],x[i]*x[j]));
                end if;
            end for;
            M_tmp := Append(M_tmp,E);
        end for;
        M_tmp := Matrix(Fq,M_tmp);
        G := Append(G,M_tmp);
    end for;

    // print("G is"); G;

    repeat
        G_i := ZeroMatrix(Fq,n,n);     // create linear Combinations of G_i's
        G_j := ZeroMatrix(Fq,n,n);     // to get F_i^-1 * F_j
        
        repeat
            G_i := ZeroMatrix(Fq,n,n);
            for i in [1..m] do
                G_i +:= Random(Fq)*G[i];
            end for;
        until Determinant(G_i) ne 0;

        G_j := ZeroMatrix(Fq,n,n);
        for i in [1..m] do
            G_j +:= Random(Fq)*G[i];
        end for;

        G_ij := (G_i^-1)*G_j; 

        f := CharacteristicPolynomial(G_ij);   // f:= CharacteristicPolynomial of G12
        fac := Factorization(f);      

        //print("f and fac is"); f; fac;    

        // keep f=g^2
        pwr_sum := 0;

        for i in [1..#fac] do;
            pwr_sum := pwr_sum + fac[i][2];
        end for;

    until 2 eq pwr_sum;

    Poly_x := fac[1][1];

    A := Evaluate(Poly_x,G_ij);  //to get the kernel of fac(G12)

    // print("xxxxxxxxxxxxxxxxxxxxxxxxxxxxx");
    // print(Poly_x);
    // print("G_ij is");G_ij;
    // print("xxxxxxxxxxxxxxxxxxxxxxxxxxxxx");


    // print("xxxxxxxxxxxxxxxxxxxxxxxxxxxxx");
    // print("A = ");A;
    // print("xxxxxxxxxxxxxxxxxxxxxxxxxxxxx");


    L := KernelMatrix(Transpose(A));  

    //TODO: 是否需要转置啊！！！！我要被这个行列向量弄疯了
    V := VectorSpace(Fq,n);
    basis := [Vector(L[i]): i in [1..Nrows(L)]];


    // print("xxxxxxxxxxxxxxxxxxxxxxxxxxxxx");
    // print("1st basis is"); print(basis);
    // print("xxxxxxxxxxxxxxxxxxxxxxxxxxxxx");

    basis := ExtendBasis(basis,V); //extend the oil subspace to the invariant linear space

    basisSeq := ElementToSequence(basis);
    k := n div 2;
    T := Matrix(Fq,n,n, basisSeq[k+1..n] cat basisSeq[1..k]); //recover T'

    return Transpose(T)^-1;

end function;




// test of Task 6

function NewKeyGen(T_prime,P)
    m := #P;
    n := Nrows(T_prime);
    v := n - m;

    Fq := Parent(T_prime[1][1]);
    P1<[x]> := Parent(P[1]); //quo <>

    // A := [];
    // for i in [1..n] do
    //     B := 0;
    //     for j in [1..n] do
    //         B +:= T_prime[j][i]*x[j];
    //     end for;
    //     A := Append(A,B);
    // end for;  

    //P_prime := [Evaluate(P[i],A): i in [1..m]];
    P_prime := P;

    G := [];
    for l in [1..m] do // recover the matrix of P
        M_tmp := [];
        for i in [1..n] do
            E := [];
            for j in [1..n] do
                if not j ge i then
                    E := Append(E, 0);
                else
                    E := Append(E, MonomialCoefficient(P[l],x[i]*x[j]));
                end if;
            end for;
            M_tmp := Append(M_tmp,E);
        end for;
        M_tmp := Matrix(Fq,M_tmp);
        G := Append(G,M_tmp);
    end for;

    FM := [];
    for i in [1..m] do
        FM[i] := Transpose(T_prime)^-1 * G[i] * T_prime^-1;
    end for;

    FM;

    F_prime := [];
    for l in [1..m] do
        F_tmp := P1 ! 0;
        for i in [1..n] do
            for j in [1..n] do
                F_tmp +:= FM[l][i][j] * x[i] * x[j];
            end for;
        end for;
        F_prime[l] := F_tmp;
    end for;

    return F_prime, P_prime;
end function;


// Fq := FiniteField(31);
// n := 8;
// v := 4;
// h := [Random(Fq) : i in [1..n-v]];

// F,T,P := OVKeyGen(Fq,n,v);

// T_prime := KSAttack(P);
// F_prime, P_prime := NewKeyGen(T_prime,P);
// print("F_prime is"); F_prime; //看看形式对不对。
// sgn_prime := OVSign(h,F_prime,T_prime);
// Verify(h,P_prime,sgn_prime);









//++++++++++++++++++++++++++++++++++++++++++ Task 8 +++++++++++++++++++++++++++++++++++++++++++++++

//++++++++++++++++++++++++++++++++++++++++++ Task 8 (1) +++++++++++++++++++++++++++++++++++++++++++++++


// // RainbowKeyGen(Fq::FldFin, n::RngIntElt, v::RngIntElt, m1::RngIntElt)
// // -> F::SeqEnum, S::AlgMatElt, T::AlgMatElt, P::SeqEnum
// // n: the total number of variables in the multivariate polynomials
// // v: the number of vinegar variables for the first layer, i.e. x1, . . . , xv, 
// // m1: the size of the first layer, and then the second layer has size
// // m2 = n − v − m1,

function RainbowKeyGen(Fq,n,v,m1)

    m2 := n - v - m1;
    v1 := v;
    o1 := m1;
    v2 := v + m1;  // First layer: v, m1
    o2 := n - v - m1;  // Second layer: v + m1, n-v-m1
    m := m1 + m2;
    v := [v,v+o1,v+o1+o2];

    q := Characteristic(Fq);
    Vn := VectorSpace(Fq,n);
    Vm := VectorSpace(Fq,m);
    P<[y]>:=PolynomialRing(Fq,n);
    Pol<[x]>:=PolynomialRing(P,n); //second layer

    // linear map T -----------------------------------------------------------------------------
    repeat
        T := RandomMatrix(Fq,n,n); 
    until Determinant(T) ne 0;

    // central map F ---------------------------------------------------------------------------

    FM := [];
    F := [];

    for layer := 1 to 2 do
        for k := v[layer] -v[1] +1 to v[layer+1]-v[1] do
            F[k] := Pol ! 0;
            FM[k] := ZeroMatrix(Fq,n,n);

            for i := 1 to v[layer] do
                for j := 1 to v[layer+1] do
                    a := Random(Fq);
                    FM[k][i][j] := a;
                    F[k] +:= a* x[i]*x[j]; //TODO: x,j 要不要对称
                end for;
            end for;

        end for;
    // print("**************************");
    // print("FM is"); FM;
    // print("**************************");   

    end for;

    // linear map S ---------------------------------------------------------------------------------------
    S := ZeroMatrix(Fq,m,m);
    repeat
        S := RandomMatrix(Fq,m,m);
    until Determinant(S) ne 0;

    SM := Matrix(Pol,m,m,ChangeUniverse(Eltseq(S),Pol));

    // public key Pk ----------------------------------------------------------------------------

    FT_matrix := [];  // create the matrix T^tFT
    for i in [1..m] do
        FT_matrix[i] := Transpose(T) * FM[i] * T;
    end for;

    // print("**************************");
    // print("FT_matrix is"); FT_matrix;
    // print("**************************");   

    

    FT := ZeroMatrix(Pol,m,1);   // transfer FM to F
    for k in [1..m] do
        tmp := ZeroMatrix(Pol,n,1);
        for i in [1..n] do 
            for j in [1..n] do //generate first x_j
                tmp[i][1] +:= FT_matrix[k][i][j] * x[j] *x[i];
            end for;
        end for;

        tmp1 := Pol ! 0;
        for i in [1..n] do  //..no generate second x_i 
            tmp1 +:= tmp[i][1] ;
        end for;

        FT[k][1] := tmp1;
    end for;


    // print("**************************");   
    // print(FT);
    // print("**************************");   

    PM := SM * FT;


    
    P := ElementToSequence(PM);

    return F,S,T,P;
end function;




// // Task 8 b)
// // RainbowSign(h::SeqEnum, F::SeqEnum, m1::RngIntElt, S::AlgMatElt, T::AlgMatElt)
// // -> sgn::SeqEnum


function RainbowSign(h,F,m1,S,T)

    m := #F;
    n := Nrows(T);
    v1 := n - m;
    o1 := m1;
    o2 := n - v1 - m1;
    v := [v1,v1+o1,v1+o1+o2];
    u := #v - 1;

    Fq := Parent(T[1][1]);
    q := Characteristic(Fq);
    R := PolynomialRing(Fq,n) ;
    Pol<[x]> := PolynomialRing(R,n); //quotient rings of R


    // recover S^-1(h)
    HM := ZeroMatrix(Fq,m,1);

    for i in [1..m] do
        HM[i][1] := h[i];
    end for;

    h := ElementToSequence(S^-1*HM);

    var := [];

    repeat
        var := [Random(Fq): i in [1..v1]] cat [x[i+v1]:i in [1..m]]; //find v random values

	    poly_oil := [Evaluate(F[i],var): i in [1..m]]; // solution of values of x[v+1]..x[n]


        for i in [2..u+1] do 
            // solution for o1 equations, set by x_v1+1,x_v2
            
            o := v[i] - v[i-1];

	        V := ZeroMatrix(Fq,o,o); // Vx = y
            cons := [];
	        for i1 := v[i-1]+1-v[1] to v[i]-v[1] do
                cons := Append(cons,Fq! MonomialCoefficient(poly_oil[i1],1));
	            for j1 := v[i-1]+1 to v[i] do
	                V[j1 -v[i-1]][i1 +v[1] - v[i-1]] := Fq! MonomialCoefficient(poly_oil[i1],x[j1]); //x_v+1,..,x_n
	            end for;
	        end for;

            // solution vector
            h1 := [];
            for k := 1 to v[i] - v[i-1] do
                h1[k] := h[k + v[i-1] - v[1]];
            end for;

            // calculting X = V-1 * h
            Y := [h1[i]- cons[i]: i in [1..o]];

            fullrank := Rank(V) eq o;

            if fullrank ne true then
                //printf "No Solution for Layer %o: Choose other Vinegar Variables\n", i-1;
                break;
            end if;
            
            sol_o :=  ElementToSequence(Vector(Fq,Y) * V^-1);

            // simplify the system by substituting the values of the oil variables
            for j in [v[i-1]+1..v[i]] do
                var[j] := sol_o[j-v[i-1]]; //TODO:
            end for;
            
            for i1 := v[i] - v[1] to m do
                for j := 1 to n do 
                    poly_oil[i1] := Evaluate(poly_oil[i1],x[j],var[j]);
                end for;
            end for;

        

        end for;
        // solution for o2 equations, set by x_v1+1,x_n

    until fullrank;
    //calculating T^-1(X) = T^-1 * X = (X^T * (T^-1)^t)T, suppose X is a column vector!!!!!!
    sgn := ElementToSequence(Vector(Fq,var) * Transpose(T^-1));
    return sgn;

end function;





// test of Task 8
// n := 6;
// Fq := FiniteField(31);
// v := 2;
// m1 := 2;
// h := [23,19,0,11];
// print("h is"); h;
// F,S,T,P := RainbowKeyGen(Fq,n,v,m1);
// sgn := RainbowSign(h,F,m1,S,T);
// Verify(h,P,sgn);




// //Task 9
procedure Task9()
    r := [0,8,6,7,7,9,9];
    h := [];
    q := 16;
    n := 96;
    v := 32;
    m1 := 32;


    R<x> := PolynomialRing(GF(2));
    F16<w> := ext< GF(2) | x^4 + x + 1 >;

    h := [F16!0: i in [1..57]];
    for i in [1..7] do 
        r_i := Intseq(r[i], 2);
        for j in [#r_i+1..4] do 
            r_i := r_i cat [0];
        end for;
        r_i := Reverse(r_i);
        h := h cat [r_i[4] + r_i[3]*w + r_i[2]*w^2 + r_i[1]*w^3];
    end for;

    h;
    F,S,T,P := RainbowKeyGen(F16,n,v,m1);
    sgn := RainbowSign(h,F,m1,S,T);

    print("**************************");   
    print("sgn is:");
    print(sgn);
    if Verify(h,P,sgn) then
        print("PASS!!!!");
    else 
        print("FAILED!!!!");
    end if;
    print("**************************");   

end procedure;

Task9();