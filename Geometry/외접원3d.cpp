PT center_of_enclosing_circle (const PT &p1, const PT &p2, const PT &p3){
    // returns center of circle passing through three POINT3D : p1, p2, p3

    PT A = p1 - p3;
    PT B = p2 - p3;

    lb a = A.size();
    lb b = B.size();
    lb c = A * B;

    lb p = (a*b-b*c) / (2*a*b-2*c*c);
    lb q = (a*c-b*a) / (2*c*c-2*a*b);

    PT C = p1 * p + p2 * q + p3 * (1-p-q);

    return C;
}
