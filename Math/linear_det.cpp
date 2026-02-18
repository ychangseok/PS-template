template<class T>
Polynomial<T> linear_det(Matrix<T> A, Matrix<T> B, ll mod=0){
    // calculate det(Ax+B)
    int n = A.n;
    assert(n == A.m && n == B.n && n == B.n);
  
    int a = 0, b = 0;
    ll det = 1;

    while (a + b < n){
        for (int i = 0; i < a; i++){
            B.cadd(a, i, mod-A[{i, a}], mod);
            A.cadd(a, i, mod-A[{i, a}], mod);
        }

        for (int i = a; i < n-b; i++){
            if (A[{i, a}] != 0){
                A.rswap(a, i);
                B.rswap(a, i);
                if (i != a) det = mod - det;
                break;
            }
        }

        if (A[{a, a}] != 0){            
            det *= A[{a, a}];
            det %= mod;

            B.rmul(a, power(A[{a, a}], mod-2, mod), mod);
            A.rmul(a, power(A[{a, a}], mod-2, mod), mod);

            for (int i = a+1; i < n; i++){
                B.radd(i, a, mod-A[{i, a}], mod);
                A.radd(i, a, mod-A[{i, a}], mod);
            }
            a++;
        }else {
            int R = n - b - 1;
            A.cswap(a, R);
            B.cswap(a, R);
            if (a != R) det = mod - det;

            int pos = -1;

            for (int i = R; i >= 0; i--){
                if (B[{i, R}] != 0){
                    pos = i;
                    break;
                }
            }

            if (pos == -1){
                return Polynomial<T>();
            } else{
                if (pos < a){
                    A.rswap(pos, a-1);
                    B.rswap(pos, a-1);
                    A.cswap(pos, a-1);
                    B.cswap(pos, a-1);
                    A.rswap(a-1, R);
                    B.rswap(a-1, R);

                    if (a-1 != R) det = mod - det;
                    a--;
                }else{
                    A.rswap(pos, R);
                    B.rswap(pos, R);

                    if (pos != R) det = mod - det;
                }
                
                det *= B[{R, R}];
                det %= mod;

                A.rmul(R, power(B[{R, R}], mod-2, mod), mod);
                B.rmul(R, power(B[{R, R}], mod-2, mod), mod);
                
                for (int i = 0; i < R; i++){
                    A.radd(i, R, mod-B[{i, R}], mod);
                    B.radd(i, R, mod-B[{i, R}], mod);
                }
                b++;
            }
        }
    }

    Matrix<T> C(a);
        
    for (int i = 0; i < a; i++){
        for (int j = 0; j < a; j++){
            C[{i, j}] = mod - B[{i, j}];
            C[{i, j}] %= mod;
        }
    }

    Polynomial<T> ans = C.char_poly(mod);
    ans = ans.multiply(Polynomial<T>(vector<T>{det}), mod);

    return ans;
}
