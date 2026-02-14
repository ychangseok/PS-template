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
