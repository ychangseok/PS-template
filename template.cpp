#include <iostream>
#include <algorithm>
#include <cmath>
#include <string.h>
#include <tuple>
#include <vector>
#include <stack>
#include <queue>
#include <bitset>
#include <set>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <functional>
#include <complex>

using namespace std;

typedef long long ll;
typedef unsigned long long ull;
typedef long double lb;
typedef pair<int, int> pii;
typedef pair<int, pii> piii;
typedef pair<ll, ll> pll;
typedef pair<ll, pll> plll;
typedef pair<pll, pll> LINE;
typedef vector<ll> vll;

#define all(v) v.begin(), v.end()
#define zip(v) sort(all(v)); v.erase(unique(all(v)), v.end());
#define FAST cin.tie(0), cout.tie(0);
#define FASTIO cin.tie(0), cout.tie(0), ios::sync_with_stdio(0);
#define fr(j, n) for(int i = j; i < n + j; i++)
#define pb push_back
#define cx first
#define cy second

#define MAX 100000 
#define MOD 998_244_353
#define MOD 1_000_000_007
#define int_INF (1<<31-1)
#define PI 3.141592653589793238462

#pragma GCC optimize ("O3")
#pragma GCC optimize ("Ofast")
#pragma GCC optimize ("unroll-loops")
#pragma GCC target("avx,avx2")

int dx[4] = {-1, 0, 1, 0};
int dy[4] = {0, 1, 0, -1};

int dx[8] = {-2, -1, 1, 2, 2, 1, -1, -2};
int dy[8] = {1, 2, 2, 1, -1, -2, -2, -1};

#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
using namespace __gnu_pbds;
#define ordered_set tree<pii, null_type, less<pii>, rb_tree_tag,tree_order_statistics_node_update>

/* ================Memo to Myself===========================

std::set, stack 까먹지 않기
문제에서 특별한 언급이 없다면 self-loop / multiple edge가 주어질 수 있다

============================================================= */

// ==================================MATH=============================== 

template <class T>
class Fraction{
public:
    T p, q;

    Fraction<T>(T p_=0, T q_=0) : p(p_), q(q_) {}
    Fraction<T>(const Fraction<T> &d) : p(d.p), q(d.q) {}

    Fraction<T> operator+(Fraction<T> const&d){
        return Fraction<T>(p*d.q + q*d.p, q*d.q);
    }

    Fraction<T> operator-(Fraction<T> const&d){
        return Fraction<T>(p*d.q - q*d.p, q*d.q);
    }

    Fraction<T> operator* (Fraction<T> const&d){
        return Fraction<T> (p*d.p, q*d.q);
    }

    bool operator<(Fraction<T> const&d){
        return p*d.q < q*d.p;
    }

    bool operator<= (Fraction<T> const&d){
        return p*d.q <= q*d.p;
    }

    bool operator== (Fraction<T> const&d){
        return p*d.q == q*d.p;
    }

    lb to_lb(){
        lb x = p;
        return x/q;
    }

    void print(){
        cout << p << " / " << q << endl;
    }
};

template <class T>
class Polynomial {
public:
    int deg; // degree of Polynomial
    vector<T> coef;

    Polynomial(): deg(0), coef(vector<T> {0}) {}
    Polynomial(int n) : deg(n), coef(vector<T>(n+1)) {}
    Polynomial(vector<T> coef_) : deg(coef_.size()-1), coef(coef_) {}

    T& operator[](const int k){
        assert(0 <= k && k <= deg);
        return coef[k];
    }

    Polynomial<T> add(Polynomial<T> p, int mod=0){
        int n = max(deg, p.deg);
        Polynomial<T> poly(n);

        for (int i = 0; i <= n; i++){
            if (i <= deg){
                poly[i] += coef[i];
            }
            if (i <= p.deg){
                poly[i] += p[i];
            }
            if (mod) poly[i] %= mod;
        }
        return poly;
    }

    Polynomial<T> multiply(Polynomial<T> p, int mod=0){
        int n = deg + p.deg;
        Polynomial<T> poly(n);
        
        for (int i = 0; i <= deg; i++){
            for (int j = 0; j <= p.deg; j++){
                poly[i+j] += coef[i]*p[j];
                if (mod) poly[i+j] %= mod;
            }
        }

        return poly;
    }

    T evaluate(T x, int mod=0){
        T ans = coef[deg];
        for (int i = deg-1; i >= 0; i--){
            ans *= x;
            ans += coef[i];
            ans %= mod;
        }
        return ans;
    }

    void print(){
        cout << "Degree : " << deg << '\n';
        for (int i = 0; i <= deg; i++){
            cout << coef[i] << ' ';
        }
        cout << '\n';
    }
};

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

template<class T>
Polynomial<T> linear_det(Matrix<T> A, Matrix<T> B, ll mod=0){
    // calculate det(Ax+B)
    int n = A.n;

    assert(n == A.m && n == B.n && n == B.n);

    // A.print();
    // B.print();

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

            // cout << "A[{a, a}] != 0\n";
            
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

                    // cout << "pos < a\n";

                    A.rswap(pos, a-1);
                    B.rswap(pos, a-1);
                    A.cswap(pos, a-1);
                    B.cswap(pos, a-1);
                    A.rswap(a-1, R);
                    B.rswap(a-1, R);

                    if (a-1 != R) det = mod - det;
                    a--;
                }else{

                    // cout << "pos >= a\n";

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
        
        // cout << "a and b\n";
        // cout << a << ' ' << b << '\n';
        // cout << "Matrix A\n";
        // A.print();
        // cout << "Matrix B\n";
        // B.print();
        // cout.flush();
        // cout << "Det : " << det << endl;
        // Polynomial<T> ans = naive(A, B, MOD);
        // ans = ans.multiply(Polynomial<T>(vector<T>{det}), mod);
        // ans.print();
        // cout << "-----------------------\n";
    }

    

    Matrix<T> C(a);
        
    for (int i = 0; i < a; i++){
        for (int j = 0; j < a; j++){
            C[{i, j}] = mod - B[{i, j}];
            C[{i, j}] %= mod;
        }
    }

    // cout << "Matrix C\n";
    // C.print();
    // cout.flush();

    Polynomial<T> ans = C.char_poly(mod);
    ans = ans.multiply(Polynomial<T>(vector<T>{det}), mod);

    return ans;
}

ll phi(ll n){
	map<ll, ll> m;
	map<ll, ll>::iterator iter;
	if (n == 1){
		return 1;
	}
	ll a = 2;
	while(a*a <= n){
		if (n % a == 0){
			m[a]++;
			n /= a;
			continue;
		}
		a++;
	}
	m[n]++;
	
	ll ans = 1;
	for(iter = m.begin(); iter != m.end(); iter++){
		ans *= pow(iter->first, iter->second) - pow(iter->first, iter->second - 1);
	}
	return ans;
}
ll power(ll x, ll y){
    if (y == -1) return power(x, MOD-2);
	ll res = 1;
	while (y){
		if (y % 2 == 1){
			res = res * x % MOD;
		}
		y /= 2;
        x = x * x % MOD;
	}
	res %= MOD;
	return res;
}
ll gcd(ll x, ll y){
	return y?gcd(y,x%y):x;
}

ll discrete_log(ll p, ll g, ll h){
	// baby step giant step
	// O(sqrt{p} log p)
	
	// find x in [0, P) such that
	// g^x == h (mod p)
	// g is primitive root of  p
	// p is prime
	
	map<ll, ll> m;
	
	ll b = ll(sqrt(p-1)) + 1;
		
	for (ll v = 0; v < b; v++){
		ll tmp = power(g, p-2, p);
		m.insert({mul(h, power(tmp, v, p), p), v});
	}
		
	ll ans = p;
	g = power(g, b, p);
	for (ll u = 0; u < b; u++){
		ll tmp = power(g, u, p);
		if (m.find(tmp) != m.end()){
			ans = u*b + m[tmp];
			break;
		}
	}
	
	return ans;
}

void lucy_hedgehog(){
    // count number of primes under N in O(n^3/4)
    ll i, j;
    for (i = 1; i <= C; i++){
        A[i] = i-1;
        B[i] = tmp[i] - 1;
    }

    for (i = 2; i <= C; i++){
        if (!isprime[i]) continue;
        
        for (j = 1; j <= C; j++){
            if (tmp[j] < i*i) break;

            B[j] -= get(tmp[j]/i) - num_pr[i-1];
        }

        for (j = C; j >= 1; j--){
            if (j < i*i) break;
            A[j] -= get(j/i) - num_pr[i-1];
        }
    }
}

// 재귀
void fft(vector<complex<long double> > &P, bool inverse=false){
    int n = P.size();
    if (n == 1) return;

    const long double PI = 3.141592653589793238462;

    complex<long double> unit(cos(2*PI/n), sin(2*PI/n));
    if (inverse) unit = conj(unit);

    vector<complex<long double> > even, odd;
    for (int i = 0; i < n; i++){
        if (i % 2 == 0) even.push_back(P[i]);
        else            odd.push_back(P[i]);
    }

    fft(even, inverse);
    fft(odd, inverse);

    complex<long double> w(1);
    for (int i = 0; i < n/2; i++){
        P[i] = even[i] + w * odd[i];
        P[i+n/2] = even[i] - w * odd[i];
        w *= unit;
    }
}
// 비재귀
void fft(vector<complex<double> > &P, bool inverse=false){
    int n = P.size();
    if (n == 1) return;

    const double PI = 3.141592653589793238462;

    for (int i = 0; i < n; i++){
        // shift =  bit reversal of i 
        int shift = 0, size = n, idx = i;
        while (size > 1){
            if (idx & 1) shift += size >> 1;
            size >>= 1;
            idx >>= 1;
        }
        if (shift < i) swap(P[shift], P[i]);
    }

    for (int i = 1; i < n; i <<= 1){
        // n = 2*i에서 fft

        complex<double> unit(cos(PI/i), sin(PI/i));
        if (inverse) unit = conj(unit);

        for (int j = 0; j < n; j += i << 1){
            
            complex <double> w(1);
            for (int k = 0; k < i; k++){
                // x = a[j+k], y = a[i+j+k]
                // a[j+k] <- x + wy
                // a[i+j+k] <- x - wy

                complex<double> tmp = P[i+j+k] * w;
                P[i+j+k] = P[j+k] - tmp;
                P[j+k] += tmp;
                w *= unit;
            }
        }
    }


    if (inverse){
        for (int i = 0; i < n; i++){
            P[i] /= n;
        }
    }
}
// 재귀
void ntt(vector<ll> &P, bool inverse, ll g, const ll mod){
    int n = P.size();
    if (n == 1) return;

    ll unit = g;
    if (inverse) unit = power(g, mod-2, mod);

    vector<ll> even, odd;
    for (int i = 0; i < n; i++){
        if (i % 2 == 0) even.push_back(P[i]);
        else            odd.push_back(P[i]);
    }

    ntt(even, inverse, (g*g)%mod, mod);
    ntt(odd, inverse, (g*g)%mod, mod);

    ll w = 1;
    for (int i = 0; i < n/2; i++){
        P[i] = even[i] + w * odd[i];
        P[i+n/2] = even[i] + (mod - w) * odd[i];
        P[i] %= mod;
        P[i+n/2] %= mod;
        w *= unit;
        w %= mod;
    }
}
// 비재귀
void ntt(vector<ll> &P, bool inverse, ll g){
    int n = P.size();
    if (n == 1) return;

    for (int i = 0; i < n; i++){
        // shift =  bit reversal of i 
        int shift = 0, size = n, idx = i;
        while (size > 1){
            if (idx & 1) shift += size >> 1;
            size >>= 1;
            idx >>= 1;
        }
        if (shift < i) swap(P[shift], P[i]);
    }

    for (int i = 1; i < n; i <<= 1){
        // n = 2*i에서 ntt

        ll unit = power(g, n/(2*i));
        if (inverse) unit = power(unit, MOD-2);

        for (int j = 0; j < n; j += i << 1){

            ll w = 1;
            for (int k = 0; k < i; k++){
                // x = a[j+k], y = a[i+j+k]
                // a[j+k] <- x + wy
                // a[i+j+k] <- x - wy

                ll tmp = (P[i+j+k] * w) % MOD;
                P[i+j+k] = P[j+k] + MOD - tmp;
                P[j+k] += tmp;
                w *= unit;
                P[i+j+k] %= MOD;
                P[j+k] %= MOD;
                w %= MOD;
            }
        }
    }


    if (inverse){
        ll invn = power(n, MOD-2);
        for (int i = 0; i < n; i++){
            P[i] *= invn;
            P[i] %= MOD;
        }
    }
}

ll f(ll v){
    // by pani
    v |= v >> 1;
    v |= v >> 2;
    v |= v >> 4;
    v |= v >> 8;
    v |= v >> 16;
    // v |= v >> 32;
    v++;
    return v;
}
vector<ll> polymul(vector<ll> v1, vector<ll> v2){
    // cout << "Polymul" << endl;
    // NTT mod 998244353

    ll n1 = v1.size();
    ll n2 = v2.size();

    ll N = f(n1 + n2 - 1);

    v1.resize(N);
    v2.resize(N);

    ll g = power(3, 998244353 / N);
    ntt(v1, false, g);
    ntt(v2, false, g);

    vector<ll> res(N);
    for (int i = 0; i < N; i++){
        res[i] = v1[i] * v2[i];
    }

    ntt(res, true, g);

    return res;
}
vector<ll> solve(const vector<vector<ll> > &v, int left, int right){
    // cout << left << ' ' << right << endl;

    if (left == right) return v[left];

    int mid = (left + right) / 2;

    vector<ll> v1 = solve(v, left, mid);
    vector<ll> v2 = solve(v, mid+1, right);

    return polymul(v1, v2);
}
vector<ll> polypower(vector<ll> v1, ll k){
    vector<ll> res{1};
    while (k){
        if (k % 2){
            res = polymul(res, v1);
        }
        v1 = polymul(v1, v1);
        k /= 2;
    }
    return res;
}

ll crt(int n, const vector<ll> &a, const vector<ll> &p){
	// n = a.size() = p.size()
	// p의 원소들은 pairwise 서로소
    // x = a[i] (mod pi), 0 <= i < n

	ll res = 0;
	ll N = 1;
	for (int i = 0; i < n; i++) N *= p[i];

	for (int i = 0; i < n; i++){
		ll Ni = N / p[i];
		ll Mi = invmod(Ni, p[i]);
		res += a[i] * Mi * Ni % N; // overflow 가능성 있음
		res %= N;
	}

	return res;
}

//========================NEW GEOMETRY=========================

template <class T>
struct P2{
    T x, y;

    P2 (T x_=0, T y_=0){
        x = x_;
        y = y_;
    }

    P2 operator+ (const P2 &p) const{ return P2(x+p.x, y+p.y);}
    P2 operator- (const P2 &p) const{ return P2(x-p.x, y-p.y);}
    P2 operator- (){ return P2(-x, -y);}
    T operator* (const P2 &p) const{ return x*p.x + y*p.y;}
    P2 operator* (const T d) const{ return P2(x*d, y*d);}
    P2 r90() { return P2(y, -x);}
    T operator^ (const P2 &p) const{ return x*p.y-y*p.x;}
    T size() { return x*x+y*y;}
    bool operator< (const P2 &p) const{ return pair<T, T>{x, y} < pair<T, T>{p.x, p.y};}
    bool operator> (const P2 &p) const{ return pair<T, T>{x, y} > pair<T, T>{p.x, p.y};}
    bool operator<= (const P2 &p) const{ return pair<T, T>{x, y} <= pair<T, T>{p.x, p.y};}
    bool operator>= (const P2 &p) const{ return pair<T, T>{x, y} >= pair<T, T>{p.x, p.y};}
    bool operator== (const P2 &p) const{ return x==p.x && y==p.y;}
};
using PT = P2<ll>;
using polygon = vector<PT>;
PT O = PT();

struct P3{
    lb x, y, z;
    
    P3 operator+(const P3 &p) const{
        return P3{x+p.x, y+p.y, z+p.z};
    }
    P3 operator-(const P3 &p) const{
        return P3{x-p.x, y-p.y, z-p.z};
    }
    P3 operator*(lb mult){
        return P3{x*mult, y*mult, z*mult};
    }
    P3 operator^(const P3 &p) const{
        return P3{y*p.z-p.y*z, z*p.x-p.z*x, x*p.y-p.x*y};
    }
    lb norm(){
        return sqrt(x*x+y*y+z*z);
    }
};

ll ccw(const PT &p1, const PT &p2, const PT &p3){
    ll op = (p2-p1)^(p3-p1);
    return (op>0)-(op<0);
}
bool isIntersect(PT A, PT B, PT C, PT D){
    // check segment AB and segment CD intersects

	ll ab = ccw(A, B, C) * ccw(A, B, D);
	ll cd = ccw(C, D, A) * ccw(C, D, B);
    if (ab == 0 && cd == 0){
		if (A > B) swap(A, B);
		if (C > D) swap(C, D);
		return C <= B && A <= D;
	}
	return ab <= 0 && cd <= 0;
}

polygon convex_hull(polygon v){
    // monotone chain

    int n = v.size();
    int k = 0;

    if (n < 3) return v;

    polygon ans(2*n);

    sort(all(v),
        [](const PT &p1, const PT &p2) -> bool{
            if (p1.x == p2.x) return p1.y < p2.y;
            return p1.x < p2.x;
        }
    );
    
    for (int i = 0; i < n; i++){
        while (k >= 2 && ccw(ans[k-2], ans[k-1], v[i]) <= 0){
            k--;
        }
        ans[k] = v[i];
        k++;
    }

    for (int i = n- 1, t = k + 1; i > 0; i--){
        while (k >= t && ccw(ans[k-2], ans[k-1], v[i-1]) <= 0){
            k--;
        }
        ans[k] = v[i-1];
        k++;
    }

    ans.resize(k-1);
    return ans;
}

bool PointInConvexPolygon(const polygon &v, const PT &p){
	// https://github.com/justiceHui/icpc-teamnote/blob/master/code/Geometry/PointInConvexPolygon.cpp
	// v : counterclockwise

	if (ccw(v[0], v[1], p) < 0) return false;

	int l = 1;
	int r = v.size() - 1;

	while (l < r){
		int m = (l + r + 1) / 2;
		if (ccw(v[0], v[m], p) >= 0){
			l = m;
		}else{
			r = m-1;
		}
	}

	if (l == v.size() - 1){
		return isIntersect(v[0], v.back(), p, p);
	}
	return ccw(v[0], v[l], p) >= 0 && ccw(v[l], v[l+1], p) >= 0 && ccw(v[l+1], v[0], p) >= 0;
}

// 360 degree ccw angle sort centered on p
sort(all(pts),
    [&p](const PT &p1, const PT &p2) -> bool{
        if (p2 == p) return false;
        if (p1 == p) return true;
        if (p1 > p != p2 > p) return p1 < p2;
        return ccw(p, p1, p2) > 0;
    }
);

void reorder(polygon &P){
    int pos = 0;
    int n = P.size();

    for (int i = 1; i < n; i++){
        if (P[i].y < P[pos].y || (P[i].y == P[pos].y && P[i].x < P[pos].x)){
            pos = i;
        }
    }

    rotate(P.begin(), P.begin()+pos, P.end());
}
polygon minkowski_sum (polygon P, polygon Q){
    // minkowski sum of two convex polygon
    // O(|P| + |Q|)
    
    reorder(P);
    reorder(Q);

    int psz = P.size();
    int qsz = Q.size();

    polygon res;
    int i = 0;
    int j = 0;

    while (i < psz || j < qsz){
        res.push_back(P[i%psz]+Q[j%qsz]);

        ll crs = (P[(i+1)%psz]-P[i%psz])^(Q[(j+1)%qsz]-Q[j%qsz]);
        
        if (crs >= 0 && i < psz) i++;
        if (crs <= 0 && j < qsz) j++;
    }

    return res;
}

struct Line{
    PT p, d, p2;

    Line(PT a, PT b){
        p = a;
        p2 = b;
        d = b - a;
    }
};
bool line_intersect(const PT &s1, const PT &e1, const PT &s2, const PT &e2, PT &v){
    PT v1 = e1 - s1;
    PT v2 = e2 - s2;
    lb det = v1 ^ v2;
    if (det == 0) return false;
    lb s = ((s2-s1)^v2) / (v1 ^ v2);
    v = s1 + v1 * s;
    return true;
}
polygon HPI(vector<Line>& lines){
    auto bad = [](const Line &a, const Line &b, const Line &c){
        PT v;
        if (!line_intersect(a.p, a.p2, b.p, b.p2, v)) return false;
        lb cross = c.d^(v-c.p);
        return cross <= 0;
    };

    sort(all(lines),
        [](const Line &l1, const Line &l2) -> bool{
            if (l1.d < O != l2.d < O) return l1.d < l2.d;
            return (l1.d^l2.d) > 0;
        }
    );

    deque<Line> dq;

    for (auto line : lines){
        while (dq.size() >= 2 && bad(dq[dq.size()-2], dq.back(), line))
            dq.pop_back();

        while (dq.size() >= 2 && bad(dq[0], dq[1], line))
            dq.pop_front();
        
        if (dq.empty()) dq.push_back(line);
        else if ((dq.back().d ^ line.d) == 0){
            if ((dq.back().d * line.d) < 0){
                // inter is zero
                return polygon();
            }else if (((line.p-dq.back().p)^dq.back().d) < 0){
                dq.pop_back();
                dq.push_back(line);
            }
        }else if (dq.size() < 2 || !bad(dq.back(), line, dq[0]))
            dq.push_back(line);
    }

    polygon res;
    if (dq.size() >= 3){
        for (int i = 0; i < dq.size(); i++){
            int j = (i+1)%dq.size();
            PT v;
            if (!line_intersect(dq[i].p, dq[i].p2, dq[j].p, dq[j].p2, v)) continue;
            res.push_back(v);
        }
    }
    return res;
}

//===========================GEOMETRY=======================

// segment : 선분
// line : 직선

template <class T>
class POINT3D{
public:
    T x, y, z;

    POINT3D(T x_=0, T y_=0, T z_=0) : x(x_), y(y_), z(z_) {}

    POINT3D<T> operator+ (const POINT3D<T> &A){
        return POINT3D<T> (x+A.x, y+A.y, z+A.z);
    }

    POINT3D<T> operator- (const POINT3D<T> &A){
        return POINT3D<T> (x-A.x, y-A.y, z-A.z);
    }

    POINT3D<lb> mul(const lb &k){
        return POINT3D<lb> (x*k, y*k, z*k);
    }

    T dot (const POINT3D<T> &A){
        return x*A.x + y*A.y + z*A.z;
    }

    POINT3D<T> cross (const POINT3D<T> &A){
        return POINT3D(y*A.z-z*A.y, z*A.x-x*A.z, x*A.y-y*A.x);
    }

    T norm(){
        return sqrt(x*x + y*y + z*z);
    }
 
    T norm_square(){
        return x*x + y*y + z*z;
    }
 
    void normalize(){
        T l = norm();
        x /= l;
        y /= l;
        z /= l;
    }
    
    void print(){
        cout << x << ' ' << y << ' ' << z << '\n';
        cout << endl;
    }

};

template <class T>
class SPHERE{
public:
    T x, y, z;
    lb r;

    SPHERE(T x_=0, T y_=0, T z_=0, T r_=0) : x(x_), y(y_), z(z_), r(r_) {}
    SPHERE(POINT3D<T> C, T r_) : x(C.x), y(C.y), z(C.z), r(r_) {}

    POINT3D<T> center(){
        return POINT3D<T>(x, y, z);
    }

    void print(){
        cout << "Center : " << x << ' ' << y << ' ' << z << '\n';
        cout << "Radius : " << r << '\n';
        cout << endl;
    }
};

template <class T>
class POINT{
public:
    T x, y;
    POINT(T x_=0, T y_=0) : x(x_), y(y_) {}

    POINT<T> operator+ (const POINT<T> &A){
        return POINT<T> (x+A.x, y+A.y);
    }

    POINT<T> operator- (const POINT<T> &A){
        return POINT<T> (x-A.x, y-A.y);
    }

    bool operator==(const POINT<T>& p){
        return p.x == x && p.y == y;
    }

    lb dist(const POINT<T> &p){
        return (*this-p).norm();
    }

    ll dist_square(const POINT<T> &p){
        return (*this-p).norm_square();
    }

    lb norm(){
        return sqrt(x*x+y*y);
    }

    ll norm_square(){
        return x*x+y*y;
    }

    T dot(const POINT<T> &p){
        return x*p.x + y*p.y;
    }

    POINT<lb> mul(lb k){
        return POINT<lb>(x*k, y*k);
    }
    
    POINT<lb> to_lb(){
        return POINT<lb>(x, y);
    }

    pair<T, T> getpos(){
        return {x, y};
    }
};


template <class T>
class CIRCLE{
public:
    T x, y;
    T r;
    CIRCLE<T>(T x_=0, T y_=0, T r_=0) : x(x_), y(y_), r(r_) {}
    CIRCLE<T>(POINT<T> p, T r_=0) : x(p.x), y(p.y), r(r_) {}

    POINT<T> center(){
        return POINT<T>(x, y);
    }

    bool point_in_circle(const POINT<T> &p){
        return p.dist(this.center()) < r;
    }
    
    bool operator <(const CIRCLE c) const{
        return r > c.r;
    }
};

class LINE{
public:
    POINT<lb> d; // direction vector
    POINT<lb> p; // point on line

    LINE(POINT<ll> p1, POINT<ll> p2) : d(POINT<lb>(p2.x-p1.x, p2.y-p1.y)), p(POINT<lb>(p1.x, p2.y)) {}
    LINE(POINT<lb> p1, POINT<lb> p2) : d(POINT<lb>(p2.x-p1.x, p2.y-p1.y)), p(p1) {}
    
    lb distance(const POINT<ll> &P){
        POINT<lb> PP(P.x, P.y);
        lb t = d.dot(p-PP) / d.dot(d);
        return (d.mul(t) + p - PP).norm();
    }
};


bool isIntersect(POINT<ll> A, POINT<ll> B, POINT<ll> C, POINT<ll> D){
    // check segment AB and segment CD intersects

	pll a = {A.x, A.y};
	pll b = {B.x, B.y};
	pll c = {C.x, C.y};
	pll d = {D.x, D.y};

	ll ab = ccw(a, b, c) * ccw(a, b, d);
	ll cd = ccw(c, d, a) * ccw(c, d, b);
	if (ab == 0 && cd == 0){
		if (a > b) swap(a, b);
		if (c > d) swap(c, d);
		return c <= b && a <= d;
	}
	return ab <= 0 && cd <= 0;
}

POINT<lb> getIntersectionPoint(POINT<ll> A, POINT<ll> B, POINT<ll> C, POINT<ll> D){
    ll x1, y1, x2, y2, x3, y3, x4, y4;

    x1 = A.getpos().first;
    y1 = A.getpos().second;
    x2 = B.getpos().first;
    y2 = B.getpos().second;
    x3 = C.getpos().first;
    y3 = C.getpos().second;
    x4 = D.getpos().first;
    y4 = D.getpos().second;

    if (x1 > x2){
        swap(x1, x2);
        swap(y1, y2);
    } else if (x1 == x2 && y1 > y2){
        swap(y1, y2);
    }

    if (x3 > x4){
        swap(x3, x4);
        swap(y3, y4);
    } else if (x3 == x4 && y3 > y4){
        swap(y3, y4);
    }

    if ((x4 - x3) * (y2 - y1) == (x2 - x1) * (y4 - y3)){
        // same slope

        if (x1 == x4 && y1 == y4){
            return POINT<lb>(x1, y1);
        }else if (x2 == x3 && y2 == y3){
            return POINT<lb>(x2, y2);
        }
    } else{
        // different slope and intersect
        // only one intersection point

        // x1 + s(x2-x1) == x3 + t(x4-x3)
        // y1 + s(y2-y1) = y3 + t(y4-y3)
        // solve for s, t

        if (x3 != x4){
            lb x = x1*(y3-y4) + x3*(y4-y1) + x4*(y1-y3);
            x /= (x1-x2)*(y3-y4) + x3*(y2-y1) + x4*(y1-y2);
            lb y = x1*(y3-y2) + x2*(y1-y3) + x3*(y2-y1);
            y /= (x1-x2)*(y3-y4) + x3*(y2-y1) + x4*(y1-y2);

            return POINT<lb>(x1 + (x2-x1)*x, y1 + (y2-y1)*x);
        }else{
            lb x = x1 - x4;
            x /= x1 - x2;
            lb y = x1*(y3-y2) + x2*(y1-y3) + x4*(y2-y1);
            y /= (x1-x2)*(y3-y4);

            return POINT<lb>(x1 + (x2-x1)*x, y1 + (y2-y1)*x);
        }
    }
}

LINE bisect_segment(POINT<ll> A, POINT<ll> B, POINT<ll> C){
    // returns bisecting segment of angle ACB

    lb t = C.dist(B) / C.dist(A);
    POINT<lb> D = A.to_lb() + (B-A).mul(1/(1+t));

    return LINE(C.to_lb(), D);
}

//----------------------Geometry Algorithms------------------------------

bool PointInConvexPolygon(const vector<POINT<ll> > &v, const POINT <ll>&p){
	// https://github.com/justiceHui/icpc-teamnote/blob/master/code/Geometry/PointInConvexPolygon.cpp
	// v : counterclockwise

    if (v.size() == 1) return v[0].x == p.x && v[0].y == p.y;
    if (v.size() == 2) return isIntersect(v[0], v[1], p, p);
    
	if (ccw(v[0], v[1], p) < 0) return false;

	int l = 1;
	int r = v.size() - 1;

	while (l < r){
		int m = (l + r + 1) / 2;
		if (ccw(v[0], v[m], p) >= 0){
			l = m;
		}else{
			r = m-1;
		}
	}

	if (l == v.size() - 1){
		return isIntersect(v[0], v.back(), p, p);
	}
	return ccw(v[0], v[l], p) >= 0 && ccw(v[l], v[l+1], p) >= 0 && ccw(v[l+1], v[0], p) >= 0;

}

//  Graham scan
vector<POINT> convex_hull(vector<POINT> v){
    int n = v.size();
    sort(all(v), cmp);

    for (int i = 1; i < n; i++){
        v[i].p = v[i].x - v[0].x;
        v[i].q = v[i].y - v[0].y;
    }

    sort(v.begin()+1, v.end(), cmp);
    
    vector<POINT> cvh;
    stack<int> st;
    int next = 2;

    st.push(0);
    st.push(1);

    while (next < n){
        while (st.size() >= 2){
            int second = st.top(); st.pop();
            int first = st.top();

            if (ccw(v[first], v[second], v[next]) > 0){
                st.push(second);
                break;
            }
        }
        st.push(next);
        next++;
    }

    while (!st.empty()){
        cvh.push_back(v[st.top()]);
        st.pop();
    }

    reverse(all(cvh));

    return cvh;
}
//  Monotone chain
vector<POINT<ll> > convex_hull(vector<POINT<ll> > v){
    // monotone chain

    int n = v.size();
    int k = 0;

    if (n < 3) return v;

    vector<POINT<ll> > ans(2*n);

    sort(all(v),
        [](POINT<ll> p1, POINT<ll> p2) -> bool{
            if (p1.x == p2.x) return p1.y < p2.y;
            return p1.x < p2.x;
        }
    );
    
    for (int i = 0; i < n; i++){
        while (k >= 2 && ccw(ans[k-2], ans[k-1], v[i]) < 0){
            k--;
        }
        ans[k] = v[i];
        k++;
    }

    for (int i = n- 1, t = k + 1; i > 0; i--){
        while (k >= t && ccw(ans[k-2], ans[k-1], v[i-1]) < 0){
            k--;
        }
        ans[k] = v[i-1];
        k++;
    }

    ans.resize(k-1);
    return ans;
}

bool bcw(const POINT<ll> &p1, const POINT<ll> &p2, const POINT<ll> &p3, bool include_collinear=false){
    ll op = p1.x*p2.y + p2.x*p3.y + p3.x*p1.y;
    op -= p1.y*p2.x + p2.y*p3.x + p3.y*p1.x;
    return (op < 0) || (op == 0 && include_collinear);
}
bool bccw(const POINT<ll> &p1, const POINT<ll> &p2, const POINT<ll> &p3, bool include_collinear=false){
    ll op = p1.x*p2.y + p2.x*p3.y + p3.x*p1.y;
    op -= p1.y*p2.x + p2.y*p3.x + p3.y*p1.x;
    return (op > 0) || (op == 0 && include_collinear);
}
bool bcw(pll a, pll b, pll c, bool include_collinear=false){
	POINT<ll> A(a.first, a.second);
	POINT<ll> B(b.first, b.second);
	POINT<ll> C(c.first, c.second);

	return bcw(A, B, C, include_collinear);
}
bool bccw(pll a, pll b, pll c, bool include_collinear=false){
	POINT<ll> A(a.first, a.second);
	POINT<ll> B(b.first, b.second);
	POINT<ll> C(c.first, c.second);

	return bccw(A, B, C, include_collinear);
}
// included option for collinear pts
void convex_hull(vector<POINT<ll> >&  v, bool include_collinear=false){
    // monotone chain

    if (v.size() == 1)
        return;
    
    sort(all(v),
        [](POINT<ll> p1, POINT<ll> p2) -> bool{
            if (p1.x == p2.x) return p1.y < p2.y;
            return p1.x < p2.x;
        }
    );

    int n = v.size();
    POINT<ll> p1 = v[0], p2 = v.back();

    vector<POINT<ll> > up, down;
    up.push_back(p1);
    down.push_back(p1);

    for (int i = 1; i < n; i++){
        if (i == n-1 || bcw(p1, v[i], p2, include_collinear)){
            while (up.size() >= 2 && !bcw(up[up.size()-2], up[up.size()-1], v[i], include_collinear)){
                up.pop_back();
            } 
            up.push_back(v[i]);
        }
        if (i == n-1 || bccw(p1, v[i], p2, include_collinear)){
            while (down.size() >= 2 && !bccw(down[down.size()-2], down[down.size()-1], v[i], include_collinear)){
                down.pop_back();
            }
            down.push_back(v[i]);
        }
    }

    if (include_collinear && up.size() == v.size()){
        // reverse(all(v));
        return;
    }
    v.clear();

    v.insert(v.end(), all(down));
    up.pop_back();
    reverse(all(up));
    up.pop_back();
    v.insert(v.end(), all(up));
}


template <class T>
POINT3D<lb> center_of_enclosing_circle (POINT3D<T> p1, POINT3D<T> p2, POINT3D<T> p3){
    // returns center of circle passing through three POINT3D : p1, p2, p3

    POINT3D<T> A = p1 - p3;
    POINT3D<T> B = p2 - p3;

    lb a = A.norm_square();
    lb b = B.norm_square();
    lb c = A.dot(B);

    lb p = (a*b-b*c) / (2*a*b-2*c*c);
    lb q = (a*c-b*a) / (2*c*c-2*a*b);

    POINT3D<lb> C = p1.mul(p) + p2.mul(q) + p3.mul(1-p-q);

    return C;
}

CIRCLE enclosing_circle (const POINT &p1, const POINT &p2, const POINT &p3){
    // returns circle passing through three POINT : p1, p2, p3

    if ((p3.y-p2.y)*(p2.x-p1.x) == (p2.y-p1.y)*(p3.x-p2.x)){
        // three points on straight line
        return CIRCLE(POINT());
    }

    POINT A(p1.x-p3.x, p1.y-p3.y);
    POINT B(p2.x-p3.x, p2.y-p3.y);

    lb a = A.norm();
    lb b = B.norm();
    lb c = dot(A, B);

    lb p = (a*b-b*c) / (2*a*b-2*c*c);
    lb q = (a*c-b*a) / (2*c*c-2*a*b);

    POINT C(p*p1.x + q*p2.x - (-1+p+q)*p3.x, p*p1.y + q*p2.y - (-1+p+q)*p3.y);

    return CIRCLE(C, dist(C, p1));
}

template <class T>
CIRCLE<lb> minimum_enclosing_circle(vector<POINT<T> > v){
    // returns minimum_enclosing_circle that contains every POINT in v
    // O(n^3) 

    priority_queue<CIRCLE<lb> > pq;
    int n = v.size();

    for (int i = 0; i < n; i++){
        for (int j = i+1; j < n; j++){
            for (int k = j+1; k < n; k++){
                CIRCLE<lb> c = enclosing_circle<ll>(v[i], v[j], v[k]);

                bool check = true;

                for (int l = 0; l < n; l++){
                    if (v[l].to_lb().dist(c.center()) > c.r){
                        check = false;
                    }
                }

                if (check){
                    pq.push(c);
                }
            }
        }
    }

    for (int i = 0; i < n; i++){
        for (int j = i+1; j < n; j++){
            CIRCLE<lb> c((v[i].x + v[j].x)/2, (v[i].y+v[j].y)/2, v[i].dist(v[j])/2);

            bool check = true;

            for (int l = 0; l < n; l++){
                if (v[l].to_lb().dist(c.center()) > c.r){
                    check = false;
                }
            }

            if (check){
                pq.push(c);
            }
        }
    }

    return pq.top();
}

ll closestPoint(int n, vector<POINT<ll> > v){
    // returns square of distance of cloest points in v
    
    if (n == 2) return v[0].dist_square(v[1]);
    if (n == 3) return min(v[0].dist_square(v[1]), min(v[2].dist_square(v[0]), v[2].dist_square(v[1])));

    sort(all(v), cmp_x);
    ll x_mid = v[n/2].x;

    vector<POINT<ll> > v_left = vector<POINT<ll> >(v.begin(), v.begin() + n/2);
    vector<POINT<ll> > v_right = vector<POINT<ll> >(v.begin() + n/2, v.end());

    ll d1 = closestPoint(n/2, v_left);
    ll d2 = closestPoint(n-n/2, v_right);
    ll d = min(d1, d2);

    vector<POINT<ll> > w;
    for (int i = 0; i < n; i++){
        if (pow(v[i].x - x_mid, 2) <= d){
            w.push_back(v[i]);
        }
    }

    sort(all(w), cmp_y);
    int m = w.size();

    for (int i = 0; i < m; i++){
        int j = i + 1;
        while (j < m && pow(w[j].y - w[i].y, 2) <= d){
            d = min(d, w[i].dist_square(w[j]));
            j++;
        }
    }

    return d;
}

int getplane(ll x, ll y){
    if (y == 0){
        if (x > 0) return 0;
        return 4;
    }
    if (x == 0){
        if (y > 0) return 2;
        return 6;
    }

    if (x > 0 && y > 0){
        return 1;
    }
    if (x < 0 && y > 0){
        return 3;
    }
    if (x > 0 && y < 0){
        return 7;
    }
    if (x < 0 && y < 0){
        return 5;
    }
}
ll ccw(POINT<ll> s1, POINT<ll> s2){
    return s1.x*s2.y - s1.y*s2.x;
}
bool cmp (POINT<ll> s1, POINT<ll> s2){
    int d1 = getplane(s1.x, s1.y);
    int d2 = getplane(s2.x, s2.y);

    if (d1 == d2){
        if (ccw(s1, s2) == 0){
            return s1.x*s1.x + s1.y*s1.y < s2.x*s2.x + s2.y*s2.y;
        }
        return ccw(s1, s2) > 0;
    }
    return d1 < d2;
}

// ===========================GRAPH================

vector<ll> dijkstra(int start){
    vector<ll> dist(n+1);
    for(int i = 1; i <= n; i++){
		dist[i] = n*200000000;
	}

	dist[start] = 0;
	
    priority_queue<pll, vector<pll>, greater<pll> > pq;
	pq.push(make_pair(0, start));

	while(!pq.empty()){
	    ll d = pq.top().first;
		ll current = pq.top().second;
		pq.pop();
		
        if (dist[current] < d){
			continue;
		}

		for(int i = 0; i < graph[current].size(); i++){
			if (dist[graph[current][i].first] > d + graph[current][i].second){
				dist[graph[current][i].first] = d + graph[current][i].second;
				pq.push(make_pair(dist[graph[current][i].first], graph[current][i].first));
			}
		}
	}
    return dist;
}

vector<int> eulerian_path(){
    int v1 = -1, v2 = -1;
    vector<int> res;

    for (int i = 1; i <= 2*n; i++){
        if (deg[i] & 1){
            if (v1 == -1) v1 = i;
            else if (v2 == -1) v2 = i;
            else return res;
        }
    }

    if (v1 != -1){
        g[v1].insert(v2);
        g[v2].insert(v1);
        deg[v1]++;
        deg[v2]++;
    }

    int first = 0;
    for (int i = 1; i <= 2*n; i++){
        if (deg[i]){
            first = i;
            break;
        }
    }
    if (v1 != -1) first = v1;

    if (first == 0) return res;

    // cout << first << ' ' << v1 << ' ' << v2 << endl;

    stack<int> st;
    st.push(first);

    while (!st.empty()){
        int v = st.top();
        
        if (g[v].empty()){
            res.push_back(v);
            st.pop();
        }else{
            int i = (*g[v].begin());
            g[v].erase(g[v].find(i));
            g[i].erase(g[i].find(v));
            st.push(i);
        }
    }

    if (v1 != -1){
        for (int i = 0; i+1 < res.size(); i++){
            if (res[i] == v1 && res[i+1] == v2){
                vector<int> res2;
                for (int j = i+1; j < res.size(); j++){
                    res2.push_back(res[j]);
                }
                for (int j = 1; j <= i; j++){
                    res2.push_back(res[j]);
                }
                res = res2;
                break;
            }
            if (res[i] == v2 && res[i+1] == v1){
                vector<int> res2;
                for (int j = i+1; j < res.size(); j++){
                    res2.push_back(res[j]);
                }
                for (int j = 1; j <= i; j++){
                    res2.push_back(res[j]);
                }
                res = res2;
                break;
            }
        }
    }

    for (int i = 1; i <= 2*n; i++){
        if (g[i].size()){
            res.clear();
            return res;
        }
    }

    return res;
}

struct UF{
    vector<int> par, sz;
    int n;
    
    UF(int n_){
        n = n_;
        par.resize(n+1);
        sz.resize(n+1);
        init();
    }
    
    void init(){
        for (int i = 1; i <= n; i++){
            par[i] = i;
            sz[i] = 1;
        }
    }
    int get(int u){
        if (u == par[u]) return u;
        return par[u] = get(par[u]);
    }
    void merge(int u, int v){
        u = get(u);
        v = get(v);

        if (u == v) return;
        if (u > v) swap(u, v);

        par[v] = u;
        sz[u] += sz[v];
    }
    int getsz(int u){
        return sz[get(u)];
    }
    bool same(int u, int v){
        return get(u) == get(v);
    }
};

struct UFrollback{
    vector<int> par, sz, rank;
    int n;

    struct info{
        int u, v, pu, pv, szu, szv, ru, rv;
    };
    vector<info> trace;
    
    UFrollback(int n_){
        n = n_;
        par.resize(n+1);
        sz.resize(n+1);
        rank.resize(n+1);
        init();
        trace.clear();
    }
    
    void init(){
        for (int i = 1; i <= n; i++){
            par[i] = i;
            sz[i] = 1;
            rank[i] = 0;
        }
    }
    int get(int u){
        if (u == par[u]) return u;
        return get(par[u]);
    }
    void merge(int u, int v, bool perm=false){
        u = get(u);
        v = get(v);

        if (u == v) return;
        if (rank[v] > rank[u]) swap(u, v);

        if (!perm) trace.push_back({u, v, par[u], par[v], sz[u], sz[v], rank[u], rank[v]});

        par[v] = u;
        sz[u] += sz[v];
        rank[u] = max(rank[u], rank[v] + 1);
    }
    int getsz(int u){
        return sz[get(u)];
    }
    bool same(int u, int v){
        return get(u) == get(v);
    }

    void rollback(int SZ=0){
        while (trace.size() > SZ){
            info cur = trace.back();

            int u = cur.u;
            int v = cur.v;
            // par[u] = cur.pu;
            par[v] = cur.pv;
            sz[u] = cur.szu;
            rank[u] = cur.ru;
            // sz[v] = cur.szv;

            trace.pop_back();
        }
    }

};

struct RootedTreeHashing{
    const ll MOD = 998244353;
    const ll p = 9973;

    int n;
    vector<vector<int> > g;
    vector<ll> h, sz;
    vector<ll> pwp;

    RootedTreeHashing(int n_){
        n = n_;
        g.resize(n+1);
        h.resize(n+1);
        sz.resize(n+1);
        pwp.resize(n+1);

        pwp[0] = 1;
        for (int i = 1; i <= n; i++){
            pwp[i] = pwp[i-1] * p % MOD;
        }
    }

    void addEdge(int u, int v){
        g[u].push_back(v);
        g[v].push_back(u);
    }

    void hash(int cur=1, int pre=-1){
        sz[cur] = 1;
        for (int v : g[cur]){
            if (v == pre) continue;
            hash(v, cur);

            sz[cur] += sz[v];
            h[cur] += h[v] * h[v] + h[v] * pwp[sz[v]] + 42;
            h[cur] %= MOD;
        }
    }
};

struct TreeHashing{
    const vector<ll> MOD{1000000007, 998244353};
    const vector<ll> p{9973, 1557};
    const ll N = 2; // number of pair

    int n, r;
    vector<vector<int> > g;
    vector<ll> sz;
    vector<vector<ll> > h, pwp;

    TreeHashing(int n_){
        n = n_;
        r = -1;
        g.resize(n+1);
        sz.resize(n+1);

        for (int i = 0; i < N; i++){
            vector<ll> tmp(n+1);
            h.push_back(vector<ll>(n+1));
            for (int j = 1; j <= n; j++){
                tmp[j] = tmp[j-1] * p[i] % MOD[i];
            }
            pwp.push_back(tmp);
        }
    }

    void setRoot(int r_){
        r = r_;
    }

    void addEdge(int u, int v){
        g[u].push_back(v);
        g[v].push_back(u);
    }

    vector<int> getCent(){
        vector<int> centroid;

        function<void (int, int)> dfs = [&](int u, int pre){
            sz[u] = 1;
            bool is_cent = true;
            for (int v : g[u]){
                if (v == pre) continue;
                dfs(v, u);
                sz[u] += sz[v];
                if (sz[v] > n/2) is_cent = false;
            }
            if (n - sz[u] > n/2) is_cent = false;
            if (is_cent) centroid.push_back(u);
        };

        dfs(1, -1);
        return centroid;
    }

    void addRoot(){
        vector<int> cent = getCent();

        if (cent.size() == 1) r = cent[0];
        else {
            n++;
            sz.push_back(0);
            g.push_back(vector<int>());
            for (int i = 0; i < N; i++){
                h[i].push_back(0);
                pwp[i].push_back(pwp[i].back()*p[i]%MOD[i]);
            }
            
            g[cent[0]].push_back(n);
            g[cent[1]].push_back(n);
            g[n].push_back(cent[0]);
            g[n].push_back(cent[1]);
            
            for (int i = 0; i < g[cent[0]].size(); i++) if (g[cent[0]][i] == cent[1]) {g[cent[0]].erase(g[cent[0]].begin()+i); break;};
            for (int i = 0; i < g[cent[1]].size(); i++) if (g[cent[1]][i] == cent[0]) {g[cent[1]].erase(g[cent[1]].begin()+i); break;};
            r = n;
        }
    }

    void cal(int cur, int pre, int idx){
        sz[cur] = 1;
        h[idx][cur] = 0;
        for (int v : g[cur]){
            if (v == pre) continue;
            cal(v, cur, idx);

            sz[cur] += sz[v];
            h[idx][cur] += h[idx][v] * h[idx][v] + h[idx][v] * pwp[idx][sz[v]] + 42;
            h[idx][cur] %= MOD[idx];
        }
    }

    void hash(){
        if (r == -1) addRoot();
        
        for (int i = 0; i < N; i++){
            cal(r, -1, i);
        };
    }

    vector<ll> getHash(){
        hash();

        vector<ll> tmp;
        for (int i = 0; i < N; i++){
            tmp.push_back(h[i][r]);
        }
        return tmp;
    }
};

// tree -> string hashing
struct TreeHashing{
    const ll MOD = 998244353;
    const ll p = 9973;

    int n, r;
    vector<vector<int> > g;
    vector<string> h;
    vector<int> sz, par;

    TreeHashing(int n_){
        n = n_;
        r = -1;
        g.resize(n+1);
        h.resize(n+1);
        sz.resize(n+1);
        par.resize(n+1);
    }

    void setRoot(int r_){
        r = r_;
    }

    void addEdge(int u, int v){
        g[u].push_back(v);
        g[v].push_back(u);
    }

    vector<int> getCent(){
        vector<int> centroid;

        function<void (int, int)> dfs = [&](int u, int pre){
            sz[u] = 1;
            bool is_cent = true;
            for (int v : g[u]){
                if (v == pre) continue;
                dfs(v, u);
                sz[u] += sz[v];
                if (sz[v] > n/2) is_cent = false;
            }
            if (n - sz[u] > n/2) is_cent = false;
            if (is_cent) centroid.push_back(u);
        };

        dfs(1, -1);
        return centroid;
    }

    void addRoot(){
        vector<int> cent = getCent();

        if (cent.size() == 1) r = cent[0];
        else {
            n++;
            sz.push_back(0);
            h.push_back("");
            g.push_back(vector<int>());
            par.push_back(0);

            g[cent[0]].push_back(n);
            g[cent[1]].push_back(n);
            g[n].push_back(cent[0]);
            g[n].push_back(cent[1]);
            
            for (int i = 0; i < g[cent[0]].size(); i++) if (g[cent[0]][i] == cent[1]) {g[cent[0]].erase(g[cent[0]].begin()+i); break;};
            for (int i = 0; i < g[cent[1]].size(); i++) if (g[cent[1]][i] == cent[0]) {g[cent[1]].erase(g[cent[1]].begin()+i); break;};
            r = n;
        }
    }

    void cal(int cur, int pre=-1){
        h[cur] = '(';
        vector<string> tmp;

        for (int v : g[cur]){
            if (v == pre) continue;
            cal(v, cur);
            tmp.push_back(h[v]);
        }
        sort(all(tmp));
        for (string s : tmp){
            h[cur] += s;
        }
        h[cur] += ')';
    }

    void hash(){
        if (r == -1) addRoot();
        cal(r);
    }

    string getHash(){
        hash();
        // cout << h[r] << endl;
        return h[r];
    }
};

// SCC (Tarjan's algorithm)
ll d[MAX+3]; // 방문 순서
bool finished[MAX+3]; 
ll Scc[MAX+3]; // scc index
ll scc_index = 0;
ll id = 0;
vector<vector<ll> > SCCList;
stack<ll> st;

ll SCC(ll u){
    d[u] = ++id;

    st.push(u);

    ll parent = d[u];
    for (ll v : graph[u]){
        if (d[v] == 0) parent = min(parent, SCC(v));
        else if (!finished[v]) parent = min(parent, d[v]);
    }

    if (parent == d[u]){
        vector<ll> scc;

        while (true){
            ll t = st.top(); st.pop();
            scc.push_back(t);
            finished[t] = true;
            Scc[t] = scc_index;
            
            
            if (t == u) break;
        }

        SCCList.push_back(scc);
        scc_index++;
    }

    return parent;
}

void makeEdge(ll u, ll v){
    if (u > 0 && v > 0){
        graph[u+V].push_back(v);
        graph[v+V].push_back(u);
    } else if (u > 0 && v < 0){
        graph[u+V].push_back(V-v);
        graph[-v].push_back(u);
    } else if (u < 0 && v > 0){
        graph[-u].push_back(v);
        graph[V+v].push_back(V-u);
    } else if (u < 0 && v < 0){
        graph[-u].push_back(V-v);
        graph[-v].push_back(V-u);
    }
}

struct SCC{
    vector<vector<int> > graph;

    vector<int> d;
    vector<bool> finished;
    vector<int> Scc;
    int scc_index;
    int id;
    vector<vector<int> > SCCList;
    stack<int> st;
    int n;

    SCC (int n_){
        n = n_;
        init(n);
    }

    void addEdge(int u, int v){
        graph[u].push_back(v);
    }

    void init(int n_){
        n = n_;
        d.resize(n+1);
        finished.resize(n+1);
        Scc.resize(n+1);
        graph.resize(n+1);

        for (int i = 1; i <= n; i++){
            d[i] = 0;
            finished[i] = false;
            Scc[i] = 0;
            graph[i].clear();
        }
        SCCList.clear();
        scc_index = 0;
        id = 0;
    }

    int getscc(int u){
        d[u] = ++id;
        st.push(u);

        int parent = d[u];
        for (int v : graph[u]){
            if (d[v] == 0) parent = min(parent, getscc(v));
            else if (!finished[v]) parent = min(parent, d[v]);
        }

        if (parent == d[u]){
            vector<int> scc;

            while (true){
                int t = st.top(); st.pop();
                scc.push_back(t);
                finished[t] = true;
                Scc[t] = scc_index;

                if (t == u) break;
            }

            SCCList.push_back(scc);
            scc_index++;
        }

        return parent;
    }

    void getSCC(){
        for (int i = 1; i <= n; i++){
            if (d[i] == 0) getscc(i);
        }
    }
};

struct BipartiteMatching{
    int n, m;
    vector<vector<int> > graph;
    vector<int> amatch, bmatch;
    vector<int> vis;
    int visitcnt;

    BipartiteMatching(int n_, int m_){
        n = n_;
        m = m_;

        graph.resize(n+1, vector<int>());
        vis.resize(n+1, 0);
        visitcnt = 0;
    }

    void add(int u, int v){
        graph[u].push_back(v);
    }

    bool dfs(int u){
        if (vis[u] == visitcnt) return false;

        vis[u] = visitcnt;

        for (int v : graph[u]){
            if (bmatch[v] == -1 || dfs(bmatch[v])){
                amatch[u] = v;
                bmatch[v] = u;

                return true;
            }
        }
        return false;
    }
    int matching(){
        amatch = vector<int>(n+1, -1);
        bmatch = vector<int>(m+1, -1);

        int size = 0;
        for (int i = 1; i <= n; i++){
            visitcnt++;
            size += dfs(i);
        }
        return size;
    }
};

struct Flow{
    struct Edge{
        ll v, cap, cost;
    };

    vector<Edge> E;
    int edgecnt;

    int n;
    vector<vector<int> > g;

    Flow (int n_){
        n = n_;
        init();
        g.resize(n+1);
    }

    void init(){
        g.clear();
        edgecnt = 0;
        E.clear();
    }

    void addEdge(int u, int v, ll cap, ll cost=0){
        g[u].push_back(edgecnt);
        g[v].push_back(edgecnt+1);

        E.push_back({v, cap, cost});
        E.push_back({u, 0, -cost});
        edgecnt += 2;
    }
    void addBidirectionalEdge(int u, int v, ll cap, ll cost=0){
        g[u].push_back(edgecnt);
        g[v].push_back(edgecnt+1);

        E.push_back({v, cap, cost});
        E.push_back({u, cap, cost});
        edgecnt += 2;
    }

    bool spfa(int s, int t, vector<pair<int, int> >& parent, vector<ll>& d){
        fill(all(parent), make_pair(-1, -1));
        fill(all(d), 9e18);
        parent[s].first = -2;
        d[s] = 0;

        vector<bool> inQ(n+3, false);

        queue<int> q;
        q.push(s);
        inQ[s] = true;

        while (!q.empty()){
            int cur = q.front();
            q.pop();
            inQ[cur] = false;

            for (int nxt : g[cur]){
                int v = E[nxt].v;
                if (E[nxt].cap && d[cur] + E[nxt].cost < d[v]){
                    d[v] = d[cur] + E[nxt].cost;
                    parent[v] = {cur, nxt};

                    if (!inQ[v]){
                        q.push(v);
                        inQ[v] = true;
                    }
                }
            } 
        }  

        return parent[t].first != -1;
    }
    pair<ll, ll> maxflow(int s, int t){
        ll res = 0;
        ll flow = 0;
        vector<pair<int, int> > parent(n+3);
        vector<ll> d(n+3);

        while (spfa(s, t, parent, d)){

            ll new_flow = 1;
            int cur = t;
            while (cur != s){
                pair<int, int> prev = parent[cur];

                new_flow = min(new_flow, E[prev.second].cap);
                cur = prev.first;
            }
            
            cur = t;
            flow += new_flow;

            while (cur != s){
                pair<int, int> prev = parent[cur];

                res += new_flow * E[prev.second].cost;
                E[prev.second].cap -= new_flow;
                E[prev.second^1].cap += new_flow;
                cur = prev.first;
            }
        }

        return {flow, res};
    }

};

struct Dinic {
	struct Edge {
		ll v, cap, cost;
	};

	vector<Edge> E;
    int edgecnt;

    int n;
    vector<vector<int> > g;

    Dinic(int n_){
        n = n_;
        init();
        g.resize(n+1);
        work.resize(n+1);
        check.resize(n+1);
    }

    void init(){
        g.clear();
        edgecnt = 0;
        E.clear();
    }

	void addEdge(int u, int v, ll cap=1, ll cost=0) {
        g[u].push_back(edgecnt);
        g[v].push_back(edgecnt+1);

        E.push_back({v, cap, cost});
        E.push_back({u, 0, -cost});
        edgecnt += 2;
	}
    void addBidirectionalEdge(int u, int v, ll cap=1, ll cost=0){
        g[u].push_back(edgecnt);
        g[v].push_back(edgecnt+1);

        E.push_back({v, cap, cost});
        E.push_back({u, cap, cost});
        edgecnt += 2;
    }

	bool spfa(int s, int t, vector<pair<int, int> >& parent, vector<ll>& d){
        fill(all(parent), make_pair(-1, -1));
        fill(all(d), 9e18);
        parent[s].first = -2;
        d[s] = 0;

        vector<bool> inQ(n+3, false);

        queue<int> q;
        q.push(s);
        inQ[s] = true;

        while (!q.empty()){
            int cur = q.front();
            q.pop();
            inQ[cur] = false;

            for (int nxt : g[cur]){
                int v = E[nxt].v;
                if (E[nxt].cap && d[cur] + E[nxt].cost < d[v]){
                    d[v] = d[cur] + E[nxt].cost;
                    parent[v] = {cur, nxt};

                    if (!inQ[v]){
                        q.push(v);
                        inQ[v] = true;
                    }
                }
            } 
        }  

        return parent[t].first != -1;
    }

    vector<bool> check;
    vector<int> work;
    
	ll dfs(int s, int t, int now, ll flow, const vector<ll> &d) {
		check[now] = true;
		if(now == t) return flow;

		for(; work[now] < g[now].size(); work[now]++) {
			auto &e = E[g[now][work[now]]];

			if(!check[e.v] && d[e.v] == d[now] + e.cost && e.cap) {
				ll ret = dfs(s, t, e.v, min(flow, e.cap), d);

				if (ret == 0) continue;
                
                e.cap -= ret;
                E[g[now][work[now]]^1].cap += ret;
                return ret;
			}
		}

		return 0;
	}

	pair<ll, ll> flow(int s, int t) {
        ll res = 0;
        ll flow = 0;
        vector<pair<int, int> > parent(n+3);
        vector<ll> d(n+3);
        
		while(spfa(s, t, parent, d)) {
            fill(all(check), false);
            fill(all(work), 0);
            
		    ll now = 0;
			while(now = dfs(s, t, s, 1e18, d)) {
				res += d[t] * now;
				flow += now;
                fill(all(check), false);
			}
		}

		return {flow, res};
	}

};

// Heavy-light decomposition
int dep[MAX], par[MAX], sz[MAX], in[MAX], out[MAX], top[MAX];
ll idx = 0;
vector<int> adj[MAX]; // adj list
vector<int> graph[MAX];

void dfs(int v=1, int prev=-1){
    for (int u : adj[v]){
        if (u == prev) continue;

        graph[v].push_back(u);
        dfs(u, v);
    }
}
void dfs1(int v=1){
    sz[v] = 1;

    for (int &u : graph[v]){
        dep[u] = dep[v] + 1;
        par[u] = v;
        dfs1(u);
        sz[v] += sz[u];

        if (sz[u] > sz[graph[v][0]]) swap(u, graph[v][0]);
    }
}
void dfs2(int v=1){
    in[v] = ++idx;
    for (int u : graph[v]){
        top[u] = (u == graph[v][0]) ? top[v] : u;
        dfs2(u);
    }
    out[v] = idx;
}

// u-v 경로에 query
while (top[u] != top[v]){
    if (dep[top[u]] < dep[top[v]]) swap(u, v);

    ll xx = top[u];
    seg.Range_update(in[xx], in[u], 1);
    u = par[xx];
}

if (dep[u] > dep[v]) swap(u, v);
seg.Range_update(in[u], in[v], 1);

struct VertexDisjointBCC{
    vector<int> graph[N+3];

    void addEdge(int u, int v){
        graph[u].push_back(v);
        graph[v].push_back(u);
    }

    int dfsn[N+3], low[N+3], pv;
    vector<int> artpoint;

    void dfs(int u, int pre, bool isRoot){
        dfsn[u] = low[u] = ++pv;
        bool put = false;
        int child = 0;

        for (int v : graph[u]){
            if (pre == v) continue;
            if (dfsn[v]) low[u] = min(low[u], dfsn[v]);
            else{
                child++;
                dfs(v, u, false);

                if (!put && !isRoot && low[v] >= dfsn[u]){
                    put = true;
                    artpoint.push_back(u);
                }
                low[u] = min(low[u], low[v]);
            }
        }

        if (isRoot && child > 1){
            artpoint.push_back(u);
        }
    }

    int bcnt, bcc[N+3];
    vector<pair<int, int> > bridge;
    void color(int u, int col){
        bcc[u] = col;
        for (int v : graph[u]){
            if (bcc[v]) continue;
            if (low[v] <= dfsn[u]) color(v, col);
            else{
                bridge.push_back({min(u,v),max(u,v)});
                color(v, ++bcnt);
            }
        }
    }

    void init(int n){
        pv = bcnt = 0;
        for (int i = 1; i <= n; i++){
            graph[i].clear();
            dfsn[i] = low[i] = bcc[i] = 0;
        }
        bridge.clear();
        artpoint.clear();
    }
    void get_bcc(int n){
        for (int i = 1; i <= n; i++){
            if (dfsn[i]) continue;
            dfs(i, -1, true);
        }
        for (int i = 1; i <= n; i++){
            if (bcc[i]) continue;
            color(i, ++bcnt);
        }
    }    
};

struct sjh1224BCC{
    vector<int> graph[N+3];

    void addEdge(int u, int v){
        graph[u].push_back(v);
        graph[v].push_back(u);
    }

    bool vis[N+3];
    int dfsn[N+3];
    vector<int> bcc[N+3];
    vector<int> artpoint;
    vector<pair<int, int> > bridge;
    vector<vector<pair<int, int> > > bccedge;
    vector<pair<int, int> > st;

    int dfs(int u, int pre){
        dfsn[u] = st.size();
        int r = dfsn[u];
        
        for (int v : graph[u]){
            if (dfsn[v] == -1){
                st.push_back({u, v});
                int d = dfs(v, u);

                if (d >= dfsn[u]){
                    vector<pair<int, int> > tmp;
                    while (st.back() != make_pair(u, v)){
                        pair<int, int> p = st.back();
                        st.pop_back();
                        bcc[p.first].push_back(bccedge.size());
                        tmp.push_back(p);
                    }

                    st.pop_back();
                    bcc[u].push_back(bccedge.size());
                    bcc[v].push_back(bccedge.size());
                    tmp.push_back({u, v});
                    bccedge.push_back(tmp);
                }

                r = min(r, d);
            }else if (!vis[v] && v != pre){
                st.push_back({u, v});
                r = min(r, dfsn[v]);
            }
        }

        vis[u] = true;
        return r;
    }

    void init(int n){
        for (int i = 1; i <= n; i++){
            graph[i].clear();
            bcc[i].clear();
            dfsn[i] = -1;
            vis[i] = false;
        }
        bridge.clear();
        artpoint.clear();
        bccedge.clear();        
    }

    void get_bcc(int n){
        for (int i = 1; i <= n; i++){
            if (vis[i]) continue;
            dfs(i, -1);
        }
        for (int i = 1; i <= n; i++){
            sort(all(bcc[i]));
            bcc[i].erase(unique(all(bcc[i])), bcc[i].end());
        }
        for (int i = 1; i <= n; i++){
            if (bcc[i].size() > 1) 
                artpoint.push_back(i);
        }
        for (auto v : bccedge){
            if (v.size() == 1)
                bridge.push_back({min(v[0].first, v[0].second), max(v[0].first, v[0].second)});
        }

        sort(all(artpoint));
        sort(all(bridge));
    }    
};

// =======================STRING===================

vector<int> kmp(string s, string t){
    // https://m.blog.naver.com/PostView.naver?blogId=kks227&logNo=220917078260&proxyReferer=https:%2F%2Fwww.google.com%2F&trackingCode=external
    
    int n = s.length();
    int m = t.length();

    vector<int> fail(m);

    // calculate failure function
    // fail[i] = max k s.t. t[0..k-1] = t[i-k+1..i]

    for (int i = 1, j = 0; i < m; i++){
        while (j > 0 && t[i] != t[j]) j = fail[j-1];
        if (t[i] == t[j]) {
            j++;
            fail[i] = j;
        }
    }

    // string matching
    vector<int> res;

    for (int i = 0, j = 0; i < n; i++){

        while (j > 0 && s[i] != t[j]) j = fail[j-1];

        if (s[i] == t[j]){
            if (j == m - 1){
                // s[i:i+m] == t
                res.push_back(i - j + 1);
                j = fail[j];
            }else{
                j++;
            }
        }
    }

    return res;
}

vector<int> manacher(string s){
    string ss;
    for (char c : s){
        ss.push_back('#');
        ss.push_back(c);
    }
    ss.push_back('#');

    int r = -1;
    int c = -1;
    int ll = ss.length();

    vector<int> res(ll);

    for (int i = 0; i < ll; i++){
        if (i <= r){
            res[i] = min(r-i, res[c + (c-i)]);
        }

        while (i + res[i] + 1 < ll && i - res[i] - 1 >= 0 && ss[i + res[i] + 1] == ss[i - res[i] - 1]){
            res[i]++;
        }

        if (i + res[i] > r){
            c = i;
            r = i + res[i];
        }
    }

    // cout << ss << '\n';
    // for (int i : res){
    //     cout << i;
    // }
    // cout << '\n';

    return res;
}

int d, n;
vector<int> sa;
vector<int> lcp;
vector<int> pos;
bool cmp(int ii, int jj){
    if (pos[ii] != pos[jj]) return pos[ii] < pos[jj];

    ii += d;
    jj += d;
    return (ii < n && jj < n) ? (pos[ii] < pos[jj]) : (ii > jj);
}
void suffix_array(const string &s){
    // O(n log^2 n)

    n = s.length();
    sa.resize(n);
    lcp.resize(n);
    pos.resize(n);

    for (int i = 0; i < n; i++){
        sa[i] = i;
        pos[i] = s[i];
    }

    for (d = 1; ; d *= 2){
        sort(all(sa), cmp);

        vector<int> tmp(n);
        
        for (int i = 0; i < n-1; i++){
            tmp[i+1] = tmp[i] + cmp(sa[i], sa[i+1]);
        }

        for (int i = 0; i < n; i++){
            pos[sa[i]] = tmp[i];
        }

        if (tmp[n-1] == n-1) break;
    }

    // for (int i = 0; i < n; i++){
    //     cout << pos[sa[i]] << ' ';
    // }
    // cout << '\n';

    for (int i = 0, k = 0; i < n; i++, k = max(k-1, 0)){
        if (pos[i] == n-1) continue;

        for (int j = sa[pos[i]+1]; s[i+k] == s[j+k]; k++);

        lcp[pos[i]] = k;
    }

}

struct SA{
    int n, d;
    string s;
    vector<int> sa, pos, lcp, sainv;

    SA (string s_){
        s = s_;
        n = s.length();
        init();
    }

    bool cmp(int ii, int jj){
        if (pos[ii] != pos[jj]) return pos[ii] < pos[jj];

        ii += d;
        jj += d;
        return (ii < n && jj < n) ? (pos[ii] < pos[jj]) : (ii > jj);
    }
    void init(){
        sa.resize(n);
        lcp.resize(n);
        pos.resize(n);
        sainv.resize(n);

        for (int i = 0; i < n; i++){
            sa[i] = i;
            pos[i] = s[i];
        }

        for (d = 1; ; d *= 2){
            sort(all(sa), 
                [&](int ii, int jj) -> bool{
                    if (pos[ii] != pos[jj]) return pos[ii] < pos[jj];

                    int i2 = ii + d;
                    int j2 = jj + d;
                    return (i2 < n && j2 < n) ? (pos[i2] < pos[j2]) : (i2 > j2);
                }
            );

            vector<int> tmp(n);
            
            for (int i = 0; i < n-1; i++){
                tmp[i+1] = tmp[i] + cmp(sa[i], sa[i+1]);
            }

            for (int i = 0; i < n; i++){
                pos[sa[i]] = tmp[i];
            }

            if (tmp[n-1] == n-1) break;
        }

        for (int i = 0, k = 0; i < n; i++, k = max(k-1, 0)){
            if (pos[i] == n-1) continue;

            for (int j = sa[pos[i]+1]; s[i+k] == s[j+k]; k++);

            lcp[pos[i]] = k;
        }

        for (int i = 0; i < n; i++){
            sainv[sa[i]] = i;
        }
    }
};

struct Z{
    string s;
    int n;
    vector<int> z;

    // z[i] = max k s.t. s[i:i+k] == s[0:k]

    void init(string s_){
        s = s_;
        n = s.length();
        z.resize(n);

        int l = 0;
        int r = 0;
        z[0] = n;

        for (int i = 1; i < n; i++){
            if (i > r){
                l = r = i;
                while (r < n && s[r-l] == s[r]) r++;
                z[i] = r-l;
                r--;
            }else{
                int k = i - l;
                if (z[k] < r-i+1) z[i] = z[k];
                else{
                    l = i;
                    while (r < n && s[r-l] == s[r]) r++;
                    z[i] = r - l;
                    r--;
                }
            }
        }
    }

    int get(int k){
        return z[k];
    }
};

// ======================DATA_STRUCTURE============

// 세그트리
template <class T>
class segTree{
public:
    // segTree stores f([left, right])
    // needs to only change f_identity and f_merge() for different f

    segTree(vector<T> a_, int n_, T f_identity_, function<T(T, T)> func) : a(a_), n(n_), f_identity(f_identity_), f(func) {
        int maxn = getMax(n);
        tree.resize(maxn); 
        init(1, 0, n-1);
    }

    T Query(int left, int right){
        // returns f-value of segment [left, right]
        return query(1, 0, n-1, left, right);
    }

    void Update(int index, T val){
        // a[index] <- val
        update(1, 0, n-1, index, val);
    }

    void Update_diff(int index, T val){
        // a[index] += val
        Update(index, f_merge(Query(index, index), val));
    }

    T Getkth(int k){
        return getkth(1, 0, n-1, k);
    }

private:
    int n;
    T f_identity;
    vector<T> a;
    vector<T> tree;
    function<T(T, T)> f;

    int getMax(int n){
        return 4*n;
    }

    void init(int node, int start, int end){
        // initializing segment tree
        if (start == end) tree[node] = a[start];
        else{
            init(node*2, start, (start+end)/2);
            init(node*2+1, (start+end)/2+1, end);
            tree[node] = f_merge(tree[node*2], tree[node*2+1]);
        }
    }

    inline T f_merge(T lval, T rval){
        return f(lval, rval);
    }

    T query(int node, int start, int end, int left, int right){
        // node contains f-value of [start, end]
        // we want f-value of [left, right]

        if (left > end || right < start){
            return f_identity;
        }
        if (left <= start && end <= right){
            return tree[node];
        }

        T lsum = query(node*2, start, (start+end)/2, left, right);
        T rsum = query(node*2+1, (start+end)/2+1, end, left, right);
        return f_merge(lsum, rsum);
    }

    void update(int node, int start, int end, int index, T val){
        // node contains f-value of [start, end]
        // update a[index] <- val

        if (index < start || index > end){
            return;
        }

        if (start == end){
            tree[node] = val;
            return;
        }

        update(node*2, start, (start+end)/2, index, val);
        update(node*2+1, (start+end)/2+1, end, index, val);
        tree[node] = f_merge(tree[node*2], tree[node*2+1]);
    }

    T getkth(int node, int start, int end, int k){
        if (start == end) return start;

        if (tree[node*2] >= k){
            return getkth(node*2, start, (start+end)/2, k);
        }else{
            return getkth(node*2+1, (start+end)/2+1, end, k-tree[node*2]);
        }
    }

};

template <class T>
struct segTree{
    // 0-BASED
    vector<T> t;
    T id;
    int n;

    segTree(int n_, T id_){
        n = n_;
        id = id_;
        t = vector<T>(n*2, id);
    }

    inline T merge(T n1, T n2){
        if (n1.isidentity) return n2;
        if (n2.isidentity) return n1;

        return Node(
            max(n1.lsum, n1.sum + n2.lsum),
            max(n2.rsum, n1.rsum + n2.sum),
            max(n1.q, max(n1.rsum + n2.lsum, n2.q)),
            n1.sum + n2.sum
        );
    }
    inline T add(T n1, T n2){
        if (n1.isidentity) return n2;
        if (n2.isidentity) return n1;

        Node res(n1.sum + n2.sum, false);
        return res;
    }

    void update(int idx, T val){
        for (t[idx+=n] = val; idx >>= 1; ){
            t[idx] = merge(t[idx<<1], t[idx<<1|1]);
        }
    }
    void update_diff(int idx, T val){
        idx += n;
        t[idx] = add(t[idx], val);
        for (; idx >>= 1; ){
            t[idx] = merge(t[idx<<1], t[idx<<1|1]);
        }
    }

    T query(int l, int r){
        // [l, r)        
        T resl = id;
        T resr = id;
        for (l += n, r += n; l < r; l >>= 1, r >>= 1){
            if (l&1) resl = merge(resl, t[l++]);
            if (r&1) resr = merge(t[--r], resr); 
        }
        return merge(resl, resr);
    }

};

// 레이지 세그
template <class T, class S>
class lazySegTree{
public:
    // T : type of tree
    // S : type of lazy
    
    lazySegTree(vector<T> a_, int n_) : a(a_), n(n_) {
        // change from here
        f_identity = 0;
        lazy_identity = 0;
        // to here

        int maxn = getMax(n);
        tree = vector<T>(maxn, f_identity);
        lazy = vector<S>(maxn, lazy_identity);
        init(1, 0, n-1);

    }

    T Query(int left, int right){
        // returns f-value of segment [left, right]
        return query(1, 0, n-1, left, right);
    }

    void Range_update(int left, int right, S val){
        // a[i] += val for i in [left, right]
        range_update(1, 0, n-1, left, right, val);
    }
    
    void Update_diff(int index, S val){
        // a[index] += val
        Range_update(index, index, val);
    }

private:
    int n;
    T f_identity;
    S lazy_identity;
    vector<T> a;
    vector<S> lazy;
    vector<T> tree;

    int getMax(int n){
        return 4*n;
    }

    void init(int node, int start, int end){
        // initializing segment tree
        if (start == end) tree[node] = a[start];
        else{
            init(node*2, start, (start+end)/2);
            init(node*2+1, (start+end)/2+1, end);
            tree[node] = T_merge(tree[node*2], tree[node*2+1]);
        }
    }

    // change from here to 
    inline T T_merge(T lval, T rval){
        return (lval + rval);
    }

    inline S S_merge(S lval, S rval){
        // rval acts on lval

        return lval + rval;
    }

    inline void act(int node, int start, int end, S lazy){
        tree[node] += (end - start + 1) * lazy;
    }
    // here

    void lazy_update(int node, int start, int end){
        if (lazy[node] != lazy_identity){
            act(node, start, end, lazy[node]);

            if (start != end){
                lazy[node*2] = S_merge(lazy[node*2], lazy[node]);
                lazy[node*2+1] = S_merge(lazy[node*2+1], lazy[node]);
            }
            
            lazy[node] = lazy_identity;
        }
    }

    T query(int node, int start, int end, int left, int right){
        // node contains f-value of [start, end]
        // we want f-value of [left, right]

        lazy_update(node, start, end);

        if (left > end || right < start){
            return f_identity;
        }
        if (left <= start && end <= right){
            return tree[node];
        }

        T lsum = query(node*2, start, (start+end)/2, left, right);
        T rsum = query(node*2+1, (start+end)/2+1, end, left, right);
        return T_merge(lsum, rsum);
    }
    
    void range_update(int node, int start, int end, int left, int right, S val){
        // node contains f-value of [start, end]
        // update a[i] += val for i in [left, right]

        lazy_update(node, start, end);

        if (left > end || right < start){
            return;
        }

        if (left <= start && end <= right){
            act(node, start, end, val);

            if (start != end) {
                lazy[node*2] = S_merge(lazy[node*2], val);
                lazy[node*2+1] = S_merge(lazy[node*2+1], val);
            }

            return;
        }

        range_update(node*2, start, (start+end)/2, left, right, val);
        range_update(node*2+1, (start+end)/2+1, end, left, right, val);
        tree[node] = T_merge(tree[node*2], tree[node*2+1]);
    }
    
};

// 머지 소트 트리
template <class T>
class mergeSortTree{
public:
    mergeSortTree(vector<T> a_, int n_) : a(a_), n(n_) {
        int maxn = getMax(n);
        tree.resize(maxn); 
        init(1, 0, n-1);
    }

    ll Query(int left, int right, ll val, bool lower_bound = false){
        // if lower_bound = true,
        //   # of elt in [left, right] with elt <= val
        // else
        //   # of elt in [left, right] with elt>val
        return query(1, 0, n-1, left, right, val, lower_bound);
    }


private:
    int n;
    vector<T> a;
    vector<T> tree;

    int getMax(int n){
        return 4*n;
    }

    void init(int node, int start, int end){
        // initializing merge sort tree
        if (start == end) {
            tree[node] = a[start];
            return;
        }

        init(node*2, start, (start+end)/2);
        init(node*2+1, (start+end)/2+1, end);
        
        int p = start;
        int q = (start+end)/2;
        int r = end;

        vector<ll> tmp(r-p+1, 0);

        int i = 0;
        int j = 0;
        int k = 0;

        while (i <= q-p && j < r-q){
            if (tree[node*2][i] <= tree[node*2+1][j]){
                tmp[k] = tree[node*2][i];
                k += 1;
                i += 1;
            } else{
                tmp[k] = tree[node*2+1][j];
                k += 1;
                j += 1;
            }
        }

        while (i <= q-p){
            tmp[k] = tree[node*2][i];
            k += 1;
            i += 1;
        }

        while (j < r-q){
            tmp[k] = tree[node*2+1][j];
            k += 1;
            j += 1;
        }

        tree[node] = tmp;
    }

    ll query(int node, int start, int end, int left, int right, ll val, bool lower_bound=false){
        if (left > end || right < start){
            return 0;
        }
        if (left <= start && end <= right){
            if (lower_bound){
                return upper_bound(all(tree[node]), val) - tree[node].begin();
            }else{
                return tree[node].end() - upper_bound(all(tree[node]), val);
            }
        }

        ll lsum = query(node*2, start, (start+end)/2, left, right, val, lower_bound);
        ll rsum = query(node*2+1, (start+end)/2+1, end, left, right, val, lower_bound);
        return lsum + rsum;
    }

};

struct Fenwick{
    // range sum, point update

    int n;
    vector<int> tree;

    Fenwick(int n_){
        n = n_;
        while (n != (n & -n)){
            n += n & -n;
        }
        tree = vector<int>(n+1);
    }
    
    ll sum(int i){
        ll res = 0;
        while (i > 0){
            res += tree[i];
            i -= (i & -i);
        }
        return res;
    }
    ll query(int l, int r){
        return sum(r) - sum(l-1);
    }
    void add(int i, ll val){
        while (i <= n){
            tree[i] += val;
            i += (i & -i);
        }
    }
};

struct LiChaoTree{
    struct Line{
        ll a, b;
        ll get(ll x){
            return a*x+b;
        }
    };
    struct Node{
        int l, r;
        ll s, e;
        Line line;
    };

    const ll INF = 1e18;
    const Line id = {0, INF};
    
    vector<Node> tree;

    void init(ll s, ll e){
        tree.push_back({-1, -1, s, e, id});
    }

    void update(int node, Line v){
        ll s = tree[node].s;
        ll e = tree[node].e;
        ll m = (s + e) / 2;

        Line low = tree[node].line;
        Line high = v;
        if (low.get(s) > high.get(s)) swap(low, high);

        if (low.get(e) <= high.get(e)){
            tree[node].line = low;
            return;
        }

        if (low.get(m) < high.get(m)){
            tree[node].line = low;
            if (tree[node].r == -1){
                tree[node].r = tree.size();
                tree.push_back({-1, -1, m+1, e, id});
            }
            update(tree[node].r, high);
        }else{
            tree[node].line = high;
            if (tree[node].l == -1){
                tree[node].l = tree.size();
                tree.push_back({-1, -1, s, m, id});
            }
            update(tree[node].l, low);
        }
    }
    ll query(int node, ll x){
        if (node == -1) return INF;

        ll s = tree[node].s;
        ll e = tree[node].e;
        ll m = (s + e) / 2;

        if (x <= m) return min(tree[node].line.get(x), query(tree[node].l, x));
        else return min(tree[node].line.get(x), query(tree[node].r, x));
    }
};

struct Trie{
    vector<map<string, int> > node;

    Trie(){
        node.push_back(map<string, int>{});
    }

    void insert(const vector<string>& v){
        int idx = 0;
        for (string s : v){
            if (node[idx].find(s) == node[idx].end()){
                node.push_back(map<string, int>());
                node[idx].insert({s, node.size()-1});
                idx = node.size()-1;
            }else{
                idx = node[idx][s];
            }
        }   
    }

    void print(int idx=0, int lvl=0){
        for (auto s : node[idx]){
            for (int i = 0; i < lvl; i++){
                cout << "--";
            }
            cout << s.first << '\n';
            print(s.second, lvl+1);
        }
    }
};

struct BinaryTrie{
    const int SZ = 32;
    struct Node{
        int sz[2], idx[2];

        Node(){
            for (int i = 0; i < 2; i++){
                sz[i] = 0;
                idx[i] = -1;
            }
        }
    };
    vector<Node> node;

    BinaryTrie(){
        node.push_back(Node());
    }

    void insert(ll n){
        int idx = 0;

        for (int j = 0; j < SZ; j++){
            int k = (n & (1LL << (SZ-j-1))) > 0;

            if (node[idx].idx[k] == -1){
                node.push_back(Node());
                node[idx].sz[k]++;
                node[idx].idx[k] = node.size()-1;
                idx = node.size()-1;
            }else{
                node[idx].sz[k]++;
                idx = node[idx].idx[k];
            }
        }
    }

    ll maxxor(ll n){
        ll res = 0;
        int idx = 0;
        for (int j = 0; j < SZ; j++){
            int k = (n & (1LL << (SZ-j-1))) > 0;

            if (node[idx].idx[1-k] == -1){
                idx = node[idx].idx[k];
            }else{
                res += (1LL << (SZ-j-1));
                idx = node[idx].idx[1-k];
            }
        }

        return res;
    }
};

// ============================MISC================
vector<ll> value_compression(const vector<ll> &v){
    vector<pair<ll, ll>> w;
    int n = v.size();
    for (int i = 0; i < n; i++){
        w.push_back({i, v[i]});
    }

    sort(all(w),
        [](pair<ll, ll> p1, pair<ll, ll> p2) -> bool{
            return p1.second < p2.second;
        }
    );


    ll cur = w[0].second;
    ll idx = 1;
    w[0].second = 1;

    for (int i = 1; i < n; i++){
        if (w[i].second == cur){
            w[i].second = idx;
        }else{
            idx++;
            cur = w[i].second;
            w[i].second = idx;
        }
    }

    sort(all(w),
        [](pair<ll, ll> p1, pair<ll, ll> p2) -> bool{
            return p1.first < p2.first;
        }
    );

    vector<ll> x;
    for (int i = 0; i < n; i++){
        x.push_back(w[i].second);
    }

    return x;
}


// Learned DLX from
// https://velog.io/@jaehyeoksong0/Knuths-Algorithm-X
// https://www.geeksforgeeks.org/implementation-of-exact-cover-problem-and-algorithm-x-using-dlx/

struct node{
	piii row;
	int size;
	node* col;
	
	node* up;
	node* down;
	node* left;
	node* right;
};
vector<piii> sol;
node innode[740][324];
bool p[740][330];
void dlx_cover(node* c){
	c->right->left = c->left;
	c->left->right = c->right;
	
	for (node* i = c->down; i != c; i = i->down){
		for (node* j = i->right; j != i; j = j->right){
			j->down->up = j->up;
			j->up->down = j->down;
			j->col->size--;
		}
	}	
}
void dlx_uncover(node* c){
	for (node* i = c->up; i != c; i = i->up){
		for (node* j = i->left; j != i; j = j->left){
			j->down->up = j;
			j->up->down = j;
			j->col->size++;
		}
	}
	
	c->right->left = c;
	c->left->right = c;
}
bool dlx_search(node* head, int k){
//	cout << "Currently at depth " << k << '\n';
//	cout.flush();
	
	if (head->right == head) return 1;
	
	node* tmp = nullptr;
	int low = INF;
	
	for (node* i = head->right; i!=head; i=i->right){
		if(i->size < low){
			if (i->size == 0) return 0;
			low = i->size;
			tmp = i;
		}
	}
	
	dlx_cover(tmp);
	
	for (node* i = tmp->down; i != tmp; i=i->down){
		sol.push_back(i->row);
		
		for (node* j = i->right; j != i; j=j->right){
			dlx_cover(j->col);
		}
		
		if (dlx_search(head, k+1)) return 1;
		else{
			sol.pop_back();
			
			for (node* j=i->left; j != i; j=j->left){
				dlx_uncover(j->col);
			}
		}
	}
	
	dlx_uncover(tmp);
	return 0;
}
int getbox(int i, int j){
	return 3*(i/3) + j/3;
}
int goUp(int i){
	return i>0 ? i-1 : ROW;
}
int goDown(int i){
	return (i+1)%(ROW+1);
}
int goLeft(int i){
	return i>0 ? i-1 : COL-1;
}
int goRight(int i){
	return (i+1)%COL;
}
void insertNode(int i, int j){
	if (i){
		innode[0][j].size++;
		innode[i][j].col = &innode[0][j];
		innode[i][j].row = make_tuple((i-1)/81, ((i-1)/9)%9, (i-1)%9);
	}
	int a, b;
				
	a = i; b = j;
	do {b = goLeft(b);} while (!p[a][b] && b != j);
	innode[i][j].left = &innode[i][b];
				
	a = i; b = j;
	do {b = goRight(b);} while (!p[a][b] && b != j);
	innode[i][j].right = &innode[i][b];
	
	a = i; b = j;
	do {a = goUp(a);} while (!p[a][b] && a != i);
	innode[i][j].up = &innode[a][j];
			
	a = i; b = j;
	do {a = goDown(a);} while (!p[a][b] && a != i);
	innode[i][j].down = &innode[a][j];	
}
void makeMatrix(node* head){
	for (int i = 0; i <= ROW; i++){
		for (int j = 0; j < COL; j++){			
			if (p[i][j]){
				insertNode(i, j);
			}
		}
	}
	
	head->right = &innode[0][0];
	head->left = &innode[0][COL-1];
	innode[0][0].left = head;
	innode[0][COL-1].right = head;
}







