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
