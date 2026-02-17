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
    bool operator< (const P2 &p) const{ return array<T, 2>{x, y} < array<T, 2>{p.x, p.y};}
    bool operator> (const P2 &p) const{ return array<T, 2>{x, y} > array<T, 2>{p.x, p.y};}
    bool operator<= (const P2 &p) const{ return array<T, 2>{x, y} <= array<T, 2>{p.x, p.y};}
    bool operator>= (const P2 &p) const{ return array<T, 2>{x, y} >= array<T, 2>{p.x, p.y};}
    bool operator== (const P2 &p) const{ return x==p.x && y==p.y;}
};
using PT = P2<ll>;
using polygon = vector<PT>;
PT O = PT();
