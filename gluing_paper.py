from sage.all import derivative, GF, EllipticCurve, Matrix, vector, Conic

# The following excerpts are quoted in the article
# fmt:off
def curve_params(E, j, T1, T2):
    xT1 = T1[0]
    xT2 = T2[0]
    xT12 = (T1 + T2)[0]
    t = (-j-2) * (xT12-xT2) / (xT12-xT1) + 1
    a = (xT1 - xT2) * (t - 1)
    b = xT2
    c = (1 - t) * T1[1]

    a1, a2, a3, a4, a6 = E.a_invariants()
    assert a1 == 0 and a3 == 0
    x = E.base_field()["x"].gen()
    P = (a*x+b)**3 + a2*(a*x+b)**2 + a4*(a*x+b) + a6
    P /= c**2
    return t, P, a, b, c

def double_coords(j, t1, t2):
    j2 = j*j
    d0 = (t1**2 - t2) / (t1**3 - 1)
    num = t1*t2 - 1
    den1 = (t1-1)*(t1-j2)*(t2-j2)
    den2 = (t1-1)*(t1-j)*(t2-j)
    den3 = (t2-1)*(t1-j)*(t1-j2)
    return d0, num / den1, num / den2, num / den3

def double_points(j, t1, t2):
    XD0, XD1, XD2, XD3 = double_coords(j, t1, t2)
    YD0, YD1, YD2, YD3 = double_coords(j**2, t2, t1)
    nodes = [(XD0, YD0), (XD1, YD1), (XD2, YD2), (XD3, YD3)]
    if nodes[0] == nodes[1]:
        return [nodes[0]] + [n for n in nodes if n != nodes[0]]
    if nodes[2] == nodes[3]:
        return [nodes[2]] + [n for n in nodes if n != nodes[2]]
    return nodes

def ramif1_coords(S, t1, t2):
    num = 4*t1**2*t2**3  - t1**2 - t2**4 - 6*t1*t2**2 + 4*t2
    den = 4*(t1**3-1)*(t2**3-1)
    x = num/den
    P = S(u=x).univariate_polynomial()
    if P.degree() >= 2:
        quo, gcd = P.quo_rem(derivative(P))
        if gcd == 0:
            gcd = quo
        y = -gcd[0]/gcd[1]
        return (x, y)
    assert P.degree() == 0
    return (x, None)

def rational_sextic(P1, P2, nodes):
    assert P1[3] == 1 and P2[3] == 1
    K = P1.base_ring()
    R = K["u", "v"]
    u, v = R.gens()
    # Information from lines at infinity
    S_inf = u**3*v**3 \
        + (v**3 * (u**2*P1[2] + u*P1[1] + P1[0])) \
        + (u**3 * (v**2*P2[2] + v*P2[1] + P2[0]))
    dS_du = derivative(S_inf, u)
    dS_dv = derivative(S_inf, v)

    rows = []
    vals = []
    degrees = [(i, j) for i in range(3) for j in range(3)]
    for xN, yN in nodes:
        rows.append([xN**i * yN**j for i, j in degrees])
        vals.append(-K(S_inf(u=xN, v=yN)))
        rows.append([i*xN**(i-1)*yN**j if i > 0 else 0 for i, j in degrees])
        vals.append(-K(dS_du(u=xN, v=yN)))
        rows.append([j*xN**i*yN**(j-1) if j > 0 else 0 for i, j in degrees])
        vals.append(-K(dS_dv(u=xN, v=yN)))
    if len(nodes) == 2: # triple point
        dS_du2 = derivative(dS_du, u)
        dS_duv = derivative(dS_du, v)
        dS_dv2 = derivative(dS_dv, v)
        xN, yN = nodes[0]
        vals.append(-K(dS_du2(u=xN, v=yN)))
        rows.append([2 * yN**j if i == 2 else 0 for i, j in degrees])
        vals.append(-K(dS_dv2(u=xN, v=yN)))
        rows.append([2 * xN**i if j == 2 else 0 for i, j in degrees])
        vals.append(-K(dS_duv(u=xN, v=yN)))
        rows.append([0, 0, 0, 0, 1, 2*yN, 0, 2*xN, 4*xN*yN])

    M = Matrix(K, rows)
    coef = M.solve_right(vector(K, vals))
    S_rest = sum(c * u**i * v**j for c, (i, j) in zip(coef, degrees))
    return S_inf + S_rest

def rational_params(S, nodes, ramif):
    K = S.base_ring()
    R = K["x", "y", "z"]
    x, y, z = R.gens()

    if ramif in nodes:
        nodes = [ramif] + [n for n in nodes if n != ramif]
    x0, y0 = nodes[0]
    S = S(x, y).homogenize(var=z)
    S1 = S(x + x0*z, y + y0*z, z)

    Q = div_monom(S1(y*z, z*x, x*y), x**3 * y**3 * z**2)
    T = K["T"].gen() # Uniformizer
    if len(nodes) == 2: # triple point
        Q = div_monom(Q, z) # nodal cubic
        x1, y1 = nodes[1]
        qx1, qy1, qz1 = (y1-y0, x1-x0, (x1-x0)*(y1-y0))
        QT = Q(qx1 * z + x, qy1 * z + y, qz1 * z)
        num = QT[2,0,1] + QT[1,1,1]*T + QT[0,2,1]*T**2
        den = QT[3,0,0] + QT[2,1,0]*T + QT[1,2,0]*T**2 + QT[0,3,0]*T**3
        xQT, yQT, zQT = -num, -num*T, den
        x_Q, y_Q, z_Q = qx1 * zQT + xQT, qy1 * zQT + yQT, qz1 * zQT
    else:
        (x1, y1), (x2, y2), (x3, y3) = nodes[1:4]
        M = Matrix(K, [
            [y1-y0, x1-x0, (x1-x0)*(y1-y0)],
            [y2-y0, x2-x0, (x2-x0)*(y2-y0)],
            [y3-y0, x3-x0, (x3-x0)*(y3-y0)],
        ]).transpose()
        u, v, w = M * vector([x, y, z])
        QT = Q(u, v, w)
        C = div_monom(QT(y*z, z*x, y*x), (x*y*z) ** 2)
        assert C.total_degree() == 2

        if ramif == (x0, y0):
            rat = (1, 0, 0)  # vertical tangent
        elif ramif[1] is None:
            rat = (1/(ramif[0]-x0), 0, 1)  # at infinity
        else:
            rat = (1/(ramif[0]-x0), 1/(ramif[1]-y0), 1)
        rat = M.inverse() * vector(rat)
        rat = (rat[2]/rat[0], rat[2]/rat[1])

        CT = C(rat[0]*z + x, rat[1]*z + y, z)
        # CT: ax^2+bxy+cy^2+dx+ey=0
        for Tparam in [T] + [K(a) + 1/T for a in range(7)]:
            num = CT[1,0,1] + CT[0,1,1]*Tparam
            den = CT[2,0,0] + CT[1,1,0]*Tparam + CT[0,2,0]*Tparam**2
            x_CT, y_CT, z_CT = -num, -Tparam*num, den
            if Tparam != T:
                x_CT = (x_CT*T**2).numerator()
                y_CT = (y_CT*T**2).numerator()
                z_CT = (z_CT*T**2).numerator()
            x_C, y_C, z_C = x_CT+rat[0]*z_CT, y_CT+rat[1]*z_CT, z_CT
            x_QT, y_QT, z_QT = y_C*z_C, z_C*x_C, x_C*y_C
            x_Q, y_Q, z_Q = M*vector([x_QT, y_QT, z_QT])
            if z_Q.degree() == 4:
                xQinf, yQinf = x_Q[4]/z_Q[4], y_Q[4]/z_Q[4]
                if Q(xQinf, 0, 1) != 0 and Q(0, yQinf, 1) != 0:
                    break
    x_S1, y_S1, z_S1 = y_Q*z_Q, z_Q*x_Q, x_Q*y_Q
    X = x0 + x_S1 / z_S1
    Y = y0 + y_S1 / z_S1
    return X, Y

def div_monom(f, q):
    R = f.parent()
    res = 0
    for c, m in zip(f.coefficients(), f.monomials()):
        assert R.monomial_divides(q, m)
        res += c * R.monomial_quotient(m, q)
    return res

def triple_cover(E1, T11, T12, E2, T21, T22):
    K = E1.base_field()
    j = T11.weil_pairing(T12, 3)
    if j*j == T21.weil_pairing(T22, 3):
        T22 = -T22
    assert j == T21.weil_pairing(T22, 3)
    t1, P1, a1, b1, c1 = curve_params(E1, j, T11, T12)
    t2, P2, a2, b2, c2 = curve_params(E2, j, T21, T22)
    nodes = double_points(j, t1, t2)
    S = rational_sextic(P1.monic(), P2.monic(), nodes)
    ramif = ramif1_coords(S, t1, t2)
    assert ramif is not None
    X1, X2 = rational_params(S, nodes, ramif=ramif)
    NumX1, DenX1 = X1.numerator(), X1.denominator()
    NumX2, DenX2 = X2.numerator(), X2.denominator()
    if max(pol.degree() for pol in [NumX1, DenX1, NumX2, DenX2]) <= 2:
        return "H is singular", None, None
    Z1 = (P1(NumX1 / DenX1) * DenX1**3).numerator() // DenX2
    aZ1 = Z1.lc()
    Y1 = Z1.monic().sqrt()
    Z2 = (P2(NumX2 / DenX2) * DenX2**3).numerator() // DenX1
    aZ2 = Z2.lc()
    Y2 = Z2.monic().sqrt()
    u1 = NumX1[3] / DenX1[3]
    u2 = NumX2[3] / DenX2[3]
    T = (t1**3-1)*(t2**3-1)
    aZ12 = t1*u1+t2*u2-u1*u2*(t1*t2+2) - (1 + 2*(t1*t2-1)**3/T)/K(3)
    assert aZ12**2 == aZ1*aZ2

    def f1(x, y):
        return (a1*NumX1(x)/DenX1(x)+b1, c1*Y1(x)/DenX1(x)**2 * y)
    def f2(x, y):
        return (a2*NumX2(x)/DenX2(x)+b2, c2*Y2(x)/DenX2(x)**2 * y * aZ2 / aZ12)
    H = aZ1*DenX1*DenX2
    return H, f1, f2
# fmt:on

if __name__ == "__main__":
    K = GF(4099)
    R = K["x", "y"]
    x, y = R.gens()
    E1 = EllipticCurve(K, [-961, -1125])
    T11, T12 = E1.abelian_group().torsion_subgroup(3).gens()
    E2 = EllipticCurve(K, [1044, 354])
    T21, T22 = E2.abelian_group().torsion_subgroup(3).gens()

    H, f1, f2 = triple_cover(E1, T11.element(), T12.element(), E2, T21.element(), T22.element())
    print("H:", H)
    print("H->E1:", f1(x, y))
    print("H->E2:", f2(x, y))

    ok = 0
    for xH in K:
        if H(xH) != 0 and H(xH).is_square():
            yH = H(xH).sqrt()
            x1, y1 = f1(xH, yH)
            assert (x1, y1) in E1
            x2, y2 = f2(xH, yH)
            assert (x2, y2) in E2
            ok += 1
    print(f"Tested {ok} points")

