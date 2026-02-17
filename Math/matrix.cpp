template <class T>
class Matrix {
public:
    int n, m; // Matrix is n*m matrix
    vector<int> cidx;
    vector<vector<T> > entry;

    Matrix(int n_, int m_, vector<vector<T> > entry_) : n(n_), m(m_), entry(entry_) {init();}
    Matrix(int n_, vector<vector<T> > entry_) : Matrix(n_, n_, entry_) {}
    Matrix(int n_, int m_) : n(n_), m(m_), entry(n_, vector<T>(m_)) {init();}
    Matrix(int n_) : Matrix(n_, n_) {}
    Matrix(vector<vector<T> > entry_) : n(entry_.size()), m(entry_[0].size()), entry(entry_) {init();}

    void getInput(){
        for (int i = 0; i < n; i++){
            for (int j = 0; j < m; j++){
                cin >> entry[i][j];
            }
        }
    }
	
    void init() {
        for (int i = 0; i < m; i++){
            cidx.push_back(i);
        }
    }

    T& operator[](const pair<int, int>& p){
        assert(0 <= p.first && p.first < n);
        assert(0 <= p.second && p.second < m);

        return entry[p.first][cidx[p.second]];
    }
    
    void makeUnit(){
        for (int i = 0; i < n; i++){
            entry[i][cidx[i]] = 1;
        }
    }

    Matrix<T> add (Matrix M, const ll mod=0){
        assert(M.n==n && M.m==m);

        Matrix<T> res(n, m);

        for (int i = 0; i < n; i++){
            for (int j = 0; j < m; j++){
                res[{i, j}] = entry[i][cidx[j]] + M[{i, j}];
                if (mod) res[{i, j}] %= mod;
            }
        }
        
        return res;
    }
    
    Matrix<T> multiply (Matrix<T> M, const ll mod=0){
        // A.multiply(M) returns AM
        assert (m == M.n);

        Matrix<T> C(n, M.m);

        for (int i = 0; i < C.n; i++){
            for (int k = 0; k < m; k++){
                for (int j = 0; j < C.m; j++){
                    C[{i, j}] += entry[i][cidx[k]] * M[{k, j}];
                    if (mod) C[{i, j}] %= mod;
                }
            }
        }

        return C;
    }

    Matrix<T> power(ll N, const ll mod){
        assert (mod > 0);
        assert (n == m);

        Matrix<T> res(n);
        Matrix<T> A(n, this->entry);
        res.init();
        A.init();

        res.makeUnit();

        while (N > 0){
            if (N % 2 == 1){
                res = res.multiply(A, mod);
            }
            N /= 2;
            A = A.multiply(A, mod);
        }

        return res;       
    }

    void rswap(int i, int j){
        swap(entry[i], entry[j]);
    }
    void rmul(int i, T x, const ll mod=0){
        for (int j = 0; j < m; j++){
            entry[i][cidx[j]] *= x;
            if (mod) entry[i][cidx[j]] %= mod;
        }
    }
    void radd(int i1, int i2, T x, const ll mod=0){
        for (int j = 0; j < m; j++){
            entry[i1][cidx[j]] += entry[i2][cidx[j]] * x;
            if (mod) entry[i1][cidx[j]] %= mod;
        }
    }
    
    void cswap(int i, int j) {
        swap(cidx[i], cidx[j]);
    }
    void cmul(int j, T x, const ll mod=0) {
        for (int i = 0; i < n; i++) {
            entry[i][cidx[j]] *= x;
            if (mod) entry[i][cidx[j]] %= mod;
        }
    }
    void cadd(int j1, int j2, T x, const ll mod=0) {
        for (int i = 0; i < n; i++) {
            entry[i][cidx[j1]] += entry[i][cidx[j2]] * x;
            if (mod) entry[i][cidx[j1]] %= mod;
        }
    }

    Matrix<T> gaussian_elimination(const ll mod=0){
        // Suppose mod is prime or 0

        Matrix<T> A(n, m, entry);
        for (int j = 0, r = 0; j < m && r < n; j++){
            for (int i = r; i < n; i++){
                if (A[{i, j}]){
                    A.rswap(r, i);
                    break;
                }
            }

            if (A[{r, j}]){
                A.rmul(r,  power(A[{r, j}], mod-2, mod), mod);

                for (int i = r+1; i < n; i++){
                    A.radd(i, r, mod-A[{i, j}], mod);
                }
                r++;
            }
        }

        return A;
    }

    int rank(){
        // Suppose mod is prime or 0

        Matrix<T> A(n, m, entry);
        int r = 0;

        for (int j = 0; (j < m && r < n); j++){
            for (int i = r; i < n; i++){
                if (A[{i, j}]){
                    A.rswap(r, i);
                    break;
                }
            }

            if (A[{r, j}]){
                A.rmul(r,  1/A[{r, j}]);

                for (int i = r+1; i < n; i++){
                    A.radd(i, r, -A[{i, j}]);
                }
                r++;
            }
        }
        return r;
    }

    Matrix<T> rref(const ll mod=0){
        // Suppose mod is prime or 0

        Matrix<T> A(n, m, entry);

        for (int j = 0, r = 0; j < m && r < n; j++){
            for (int i = r; i < n; i++){
                if (A[{i, j}]){
                    A.rswap(r, i);
                    break;
                }
            }

            if (A[{r, j}]){
                A.rmul(r,  power(A[{r, j}], mod-2, mod), mod);

                for (int i = 0; i < n; i++){
                    if (i != r) A.radd(i, r, mod-A[{i, j}], mod);
                }
                r++;
            }
        }

		return A;
    }
    
    Matrix<T> inverse(const ll mod=0){
        assert(n == m);

        Matrix<T> B(n, 2*n);

        for (int i = 0; i < n; i++){
            B[{i, i+n}] = 1;
            for (int j = 0; j < n; j++){
                B[{i, j}] = entry[i][cidx[j]];
            }
        }

        B = B.rref(mod);

        Matrix<T> invA(n, n);
        invA.init();

        for (int i = 0; i < n; i++){
            for (int j = 0; j < n; j++){
                invA[{i, j}] = B[{i, j+n}];
            }
        }

        return invA;
    }

    T det(const ll mod){
        assert(n == m);

        // Suppose mod is prime
        Matrix<T> A(n, entry);
        T res = 1;

        for (int j = 0; j < n; j++){
            for (int i = j; i < n; i++){
                if (A[{i, j}]){
                    if (i > j){
                        A.rswap(i, j);
                        res = mod-res;
                    }
                    break;
                }
            }

            if (A[{j, j}] == 0){
                return 0;
            }

            res *= A[{j, j}];
            A.rmul(j, power(A[{j, j}], mod-2, mod), mod);
            for (int i = j+1; i < n; i++){
                A.radd(i, j, mod-A[{i, j}], mod);
            }

            if (mod) res %= mod;
        }

        return res;
    }

    Polynomial<T> char_poly(const ll mod) {
        // return det(xI-A)
        
        Matrix<T> A(n);

        for (int i = 0; i < n; i++){
            for (int j = 0; j < n; j++){
                A[{i, j}] = entry[i][cidx[j]];
            }
        }

        for (int j = 0; j < n-2; j++){
            for (int i = j+1; i < n; i++){
                if (A[{i, j}]){
                    A.rswap(i, j+1);
                    A.cswap(i, j+1);
                    break;
                }
            }

            if (A[{j+1, j}]) {
                for (int i = j+2; i < n; i++){
                    T x = (mod - A[{i, j}])*power(A[{j+1, j}], mod-2, mod);
                    x %= mod;
                    A.radd(i, j+1, x, mod);
                    A.cadd(j+1, i, mod-x, mod);
                }
            }
        }
        
        vector<Polynomial<T> > dp(n+1);
        dp[0] = Polynomial<T>(vector<T>{1});

        for (int k = 1; k <= n; k++){

            for (int i = 0; i < k; i++){
                T tmp = 1;
                for (int j = i+2; j <= k; j++){
                    tmp *= mod - A[{j-1, j-2}];
                    tmp %= mod;
                }

                Polynomial<T> c = dp[i].multiply(Polynomial<T>(vector<T>{tmp}), mod);

                if ((k - 1 - i) % 2){
                    c = c.multiply(Polynomial<T>(vector<T>{mod-1}), mod);
                }

                if (i == k-1) {
                    c = c.multiply(Polynomial<T>(vector<T>{mod-A[{i, k-1}], 1}), mod);
                } else{
                    c = c.multiply(Polynomial<T>(vector<T>{mod-A[{i, k-1}]}), mod);
                }

                dp[k] = dp[k].add(c, mod);
            }
        }

        return dp[n];
    }

    void print(){
        for (int i = 0; i < n; i++){
            for (int j = 0; j < m; j++){
                cout << entry[i][cidx[j]] << ' ';
            }
            cout << '\n';
        }
        cout << '\n';
    }
};
