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
