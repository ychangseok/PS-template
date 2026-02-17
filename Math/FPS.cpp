template <ll M = 998244353>
struct Modint {
    using V = long long;
    V val;

    Modint() : val(0) {}
    Modint(auto y) : val(y % M) {}

    operator V() const { return val; }
    Modint operator-() const { return Modint() -= *this; }
    Modint operator+ (auto rhs) const { return Modint(*this) += rhs; }
    Modint operator- (auto rhs) const { return Modint(*this) -= rhs; }
    Modint operator* (auto rhs) const { return Modint(*this) *= rhs; }
    Modint operator/ (auto rhs) const { return Modint(*this) /= rhs; }
    Modint &operator+= (Modint rhs) { 
        val += rhs.val;
        if (val >= M) val -= M;
        return *this;
    }
    Modint &operator-= (Modint rhs) { 
        val -= rhs.val;
        if (val < 0) val += M;
        return *this;
    }
    Modint &operator*= (Modint rhs) { val = val * rhs.val % M; return *this; }
    Modint &operator/= (Modint rhs) { val = val * rhs.inv() % M; return *this; }

    // Modint inv() {return Modint(val).pow(M-2);}
//   V inv(make_unsigned<T> x=val, V m=M) { return x > 1 ? m - inv(m % x, x) * m / x : 1; }
    Modint inv(){
        V res = inv(val, M);
        return res;
    }
    V inv(ll x, ll m) {
        return x > 1 ? m - inv(m % x, x) * m / x : 1;
    }
    Modint pow(auto y) {
        if (y == 0) return Modint(1);
        if (y < 0) return Modint(val).inv().pow(-y);

        Modint ans(1);
        Modint x(val);
        while (y){
            if (y % 2) ans *= x;
            x *= x;
            y /= 2;
        }
        return ans;
    }

    friend std::ostream &operator<<(std::ostream &os, const Modint<M> &x) { return os << x.val; }
    friend std::istream &operator>>(std::istream &is, Modint<M> &x) {
        ll val_;
        is >> val_;
        x = val_;
        return is;
    }
};
using Mint = Modint<998244353>;
using Poly = vector<Mint>;

struct FPS{
public:
    Poly coef;

    FPS (Poly a) : coef(a) {};
    FPS (int n=0) {
        coef.resize(1);
        coef[0] = Mint(n);
    }

    int size() {return coef.size();};
    int deg() {return size()-1;};
    Mint& operator[](int index){
        assert (index < coef.size());
        return coef[index];
    }

    FPS operator+ (auto f){
        int sz = max(coef.size(), f.coef.size());

        FPS res;
        res.resize(sz);

        for (int i = 0; i < coef.size(); i++){
            res.coef[i] += coef[i];
        }
        for (int i = 0; i < f.coef.size(); i++){
            res.coef[i] += f.coef[i];
        }
        return res;
    }
    FPS operator- (auto f){
        int sz = max(coef.size(), f.coef.size());

        FPS res;
        res.resize(sz);

        for (int i = 0; i < coef.size(); i++){
            res.coef[i] += coef[i];
        }
        for (int i = 0; i < f.coef.size(); i++){
            res.coef[i] -= f.coef[i];
        }
        return res;
    }
    FPS operator* (auto f) {
        int sz = coef.size() + f.coef.size() - 1;
        Poly newcoef = polymul(coef, f.coef);
        newcoef.resize(sz);
        return FPS(newcoef);
    }
    FPS &operator+= (auto f){
        return *this = *this + f;
    }
    FPS &operator-= (auto f){
        return *this = *this - f;
    }
    FPS &operator*= (auto f) {
        return *this = *this * f;
    }

    void resize(int sz){
        while (coef.size() < sz) coef.push_back(Mint(0));
        while (coef.size() > sz) coef.pop_back();
    }
    void shrink(){
        while (coef.size() > 1 && coef.back() == 0) coef.pop_back();
    }
    
    FPS power(ll k){
        FPS res(1);
        FPS f = *this;
        res[0] = 1;

        while (k){
            if (k % 2) res = res * f;
            f = f * f;
            k /= 2;
        }
        return res;
    }

    FPS inv(){
        assert (coef[0] != 0);

        FPS g(Poly{Mint(coef[0]).inv()});
        FPS two(2);

        int sz = 1;
        while (sz < coef.size()){
            FPS f(*this);
            sz *= 2;
            f.resize(sz);
            FPS tmp = g * f;
            tmp.resize(sz);
            g = g * (two - tmp);
            g.resize(sz);
        }

        g.resize(coef.size());
        // g.shrink();
        return g;
    }

    FPS log(){
        assert (coef[0] != 0);

        FPS g = (*this).differenciate();
        g *= (*this).inv();
        g.resize(coef.size());
        g = g.integrate();
        g.resize(coef.size());
        // g.shrink();
        return g;
    }

    FPS differenciate(){
        FPS res;
        res.resize(coef.size()-1);

        for (int i = 1; i < coef.size(); i++){
            res.coef[i-1] = coef[i] * i;
        }
        return res;
    }
    FPS integrate(){
        // constant term is 0
        FPS res;
        res.resize(size()+1);

        for (int i = 1; i <= coef.size(); i++){
            res.coef[i] = coef[i-1] * Mint(i).inv();
        }
        return res;
    }

    FPS exp(){
        assert (coef[0] == 0);

        FPS g(1);
        FPS one(1);

        int sz = 1;
        while (sz < 2*coef.size()){
            FPS f(*this);
            sz *= 2;
            f.resize(sz);
            g = g * (f + one - g.log());
            g.resize(sz);
        }

        g.resize(coef.size());
        // g.shrink();
        return g;
    }

    void print(){
        for (int i = 0; i < coef.size(); i++){
            cout << coef[i] << ' ';
        }
        cout << endl;
    }

    Mint evaluate(Mint x){
        Mint res(0);
        for (int i = coef.size()-1; i >= 0; i--){
            res *= x;
            res += coef[i];
        }
        return res;
    }
private:
    void ntt(Poly &P, bool inverse, Mint g){
        int n = P.size();
        if (n == 1) return;

        for (int i = 1, j = 0; i < n; i++){
            int bit = n >> 1;
            for (; j & bit; bit >>= 1) j ^= bit;
            j ^= bit;
            if (i < j) swap(P[i], P[j]);
        }

        vector<Mint> w(n/2);
        w[0] = 1;
        for (int i = 1; i < n/2; i++){
            w[i] = w[i-1] * g;
        }
        
        for (int i = 1; i < n; i <<= 1){
            int nd = n / (2 * i);

            for (int j = 0; j < n; j += i << 1){
                for (int k = 0; k < i; k++){
                    Mint tmp = P[i+j+k] * w[nd * k];
                    P[i+j+k] = P[j+k] - tmp;
                    P[j+k] += tmp;
                }
            }
        }

        if (inverse){
            Mint invn = Mint(n).inv();
            for (int i = 0; i < n; i++){
                P[i] *= invn;
            }
        }
    }
    Poly polymul(Poly v1, Poly v2){
        ll n1 = v1.size();
        ll n2 = v2.size();

        ll N = 1;
        while (N <= n1+n2-1) N *= 2;

        v1.resize(N);
        v2.resize(N);

        Mint g = Mint(3).pow(998244353 / N);

        ntt(v1, false, g);
        ntt(v2, false, g);

        Poly res;
        res.resize(N);

        for (int i = 0; i < N; i++){
            res[i] = v1[i] * v2[i];
        }
        
        ntt(res, true, g.inv());

        return res;
    }
};
