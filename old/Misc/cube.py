class Cube:
    u = []
    f = []
    l = []
    r = []
    b = []
    d = []

    def __init__(self, capital=False):
        if capital:
            self.u = ["W" for _ in range(9)]
            self.f = ["G" for _ in range(9)]
            self.l = ["O" for _ in range(9)]
            self.r = ["R" for _ in range(9)]
            self.b = ["B" for _ in range(9)]
            self.d = ["Y" for _ in range(9)]
        else:
            self.u = ["w" for _ in range(9)]
            self.f = ["g" for _ in range(9)]
            self.l = ["o" for _ in range(9)]
            self.r = ["r" for _ in range(9)]
            self.b = ["b" for _ in range(9)]
            self.d = ["y" for _ in range(9)]

    def get_input(self):
        a = []
        for i in range(9):
            a.append(list(map(str, input().split())))

        inp = [a[0] + a[1] + a[2], a[3][:3] + a[4][:3] + a[5][:3], a[3][3:6] + a[4][3:6] + a[5][3:6],
               a[3][6:9] + a[4][6:9] + a[5][6:9], a[3][9:] + a[4][9:] + a[5][9:], a[6] + a[7] + a[8]]
        self.u = inp[0]
        self.l = inp[1]
        self.f = inp[2]
        self.r = inp[3]
        self.b = inp[4]
        self.d = inp[5]

    def print_white_side(self):
        for i in range(3):
            for j in range(3):
                print(self.u[3*i+j], end='')
            print()

    def print_all(self):
        uu = self.u
        ff = self.f
        ll = self.l
        rr = self.r
        bb = self.b
        dd = self.d
        print("         {} {} {}".format(uu[0], uu[1], uu[2]))
        print("         {} {} {}".format(uu[3], uu[4], uu[5]))
        print("         {} {} {}".format(uu[6], uu[7], uu[8]))
        print("{} {} {} {} {} {} {} {} {} {} {} {}".format(ll[0], ll[1], ll[2], ff[0], ff[1], ff[2], rr[0], rr[1], rr[2], bb[0], bb[1], bb[2]))
        print("{} {} {} {} {} {} {} {} {} {} {} {}".format(ll[3], ll[4], ll[5], ff[3], ff[4], ff[5], rr[3], rr[4], rr[5], bb[3], bb[4], bb[5]))
        print("{} {} {} {} {} {} {} {} {} {} {} {}".format(ll[6], ll[7], ll[8], ff[6], ff[7], ff[8], rr[6], rr[7], rr[8], bb[6], bb[7], bb[8]))
        print("         {} {} {}".format(dd[0], dd[1], dd[2]))
        print("         {} {} {}".format(dd[3], dd[4], dd[5]))
        print("         {} {} {}".format(dd[6], dd[7], dd[8]))

    def L(self):
        ll = self.l
        uu = self.u
        bb = self.b
        ff = self.f
        dd = self.d

        ll[0], ll[2], ll[6], ll[8] = ll[6], ll[0], ll[8], ll[2]
        ll[1], ll[3], ll[5], ll[7] = ll[3], ll[7], ll[1], ll[5]
        uu[0], ff[0], dd[0], bb[8] = bb[8], uu[0], ff[0], dd[0]
        uu[6], ff[6], dd[6], bb[2] = bb[2], uu[6], ff[6], dd[6]
        uu[3], ff[3], dd[3], bb[5] = bb[5], uu[3], ff[3], dd[3]

    def L_prime(self):
        self.L()
        self.L()
        self.L()

    def U(self):
        ll = self.l
        uu = self.u
        bb = self.b
        ff = self.f
        rr = self.r

        uu[0], uu[2], uu[6], uu[8] = uu[6], uu[0], uu[8], uu[2]
        uu[1], uu[3], uu[5], uu[7] = uu[3], uu[7], uu[1], uu[5]
        ll[1], ff[1], rr[1], bb[1] = ff[1], rr[1], bb[1], ll[1]
        ll[0], ff[0], rr[0], bb[0] = ff[0], rr[0], bb[0], ll[0]
        ll[2], ff[2], rr[2], bb[2] = ff[2], rr[2], bb[2], ll[2]

    def U_prime(self):
        self.U()
        self.U()
        self.U()

    def F(self):
        ll = self.l
        uu = self.u
        ff = self.f
        dd = self.d
        rr = self.r

        ff[0], ff[2], ff[6], ff[8] = ff[6], ff[0], ff[8], ff[2]
        ff[1], ff[3], ff[5], ff[7] = ff[3], ff[7], ff[1], ff[5]
        uu[6], rr[0], dd[2], ll[8] = ll[8], uu[6], rr[0], dd[2]
        uu[8], rr[6], dd[0], ll[2] = ll[2], uu[8], rr[6], dd[0]
        uu[7], rr[3], dd[1], ll[5] = ll[5], uu[7], rr[3], dd[1]

    def F_prime(self):
        self.F()
        self.F()
        self.F()

    def D(self):
        ll = self.l
        bb = self.b
        ff = self.f
        dd = self.d
        rr = self.r

        dd[0], dd[2], dd[6], dd[8] = dd[6], dd[0], dd[8], dd[2]
        dd[1], dd[3], dd[5], dd[7] = dd[3], dd[7], dd[1], dd[5]
        ll[6], ff[6], rr[6], bb[6] = bb[6], ll[6], ff[6], rr[6]
        ll[8], ff[8], rr[8], bb[8] = bb[8], ll[8], ff[8], rr[8]
        ll[7], ff[7], rr[7], bb[7] = bb[7], ll[7], ff[7], rr[7]

    def D_prime(self):
        self.D()
        self.D()
        self.D()

    def R(self):
        uu = self.u
        bb = self.b
        ff = self.f
        dd = self.d
        rr = self.r

        rr[0], rr[2], rr[6], rr[8] = rr[6], rr[0], rr[8], rr[2]
        rr[1], rr[3], rr[5], rr[7] = rr[3], rr[7], rr[1], rr[5]
        ff[2], uu[2], bb[6], dd[2] = dd[2], ff[2], uu[2], bb[6]
        ff[8], uu[8], bb[0], dd[8] = dd[8], ff[8], uu[8], bb[0]
        ff[5], uu[5], bb[3], dd[5] = dd[5], ff[5], uu[5], bb[3]

    def R_prime(self):
        self.R()
        self.R()
        self.R()

    def B(self):
        ll = self.l
        uu = self.u
        bb = self.b
        dd = self.d
        rr = self.r

        bb[0], bb[2], bb[6], bb[8] = bb[6], bb[0], bb[8], bb[2]
        bb[1], bb[3], bb[5], bb[7] = bb[3], bb[7], bb[1], bb[5]
        uu[2], ll[0], dd[6], rr[8] = rr[8], uu[2], ll[0], dd[6]
        uu[0], ll[6], dd[8], rr[2] = rr[2], uu[0], ll[6], dd[8]
        uu[1], ll[3], dd[7], rr[5] = rr[5], uu[1], ll[3], dd[7]

    def B_prime(self):
        self.B()
        self.B()
        self.B()

    def solved(self):
        check_set = lambda x : len(set(x))

        a = 0
        a += check_set(self.l)
        a += check_set(self.u)
        a += check_set(self.r)
        a += check_set(self.f)
        a += check_set(self.b)
        a += check_set(self.u)

        return a==6
