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
