# Numerical check of the axiom-free chain for Zeta5.Hermite.pole_integral.
#  LHS  = int_0^oo wt(y)/(y^2+a^2) dy,  wt(y) = (2pi)^4 y^5/12 sum_l l^4 e^{-2 pi l y}
#  T_l  = (2 pi l)^4/12 int_0^oo y^5 e^{-2pi l y}/(y^2+a^2) dy            (LHS = sum T_l)
#  R_l  = a^4/12 int_0^oo e^{-a u} u^5/(u^2+(2 pi l)^2) du                 (T_l = R_l, u = 2 pi l y / a)
#  g(u) = 1/(e^u-1) - 1/u + 1/2 = sum_{l>=1} 2u/(u^2+4 pi^2 l^2)           (Mittag-Leffler)
#  RHS  = a^4 zeta(5,a) - 1/(2a) - 1/4 = a^4/24 int_0^oo e^{-au} u^4 g(u) du = sum R_l
from mpmath import mp, mpf, quad, nsum, exp, pi, zeta, inf
mp.dps = 30
def wt(y):
    return (2*pi)**4*y**5/12*nsum(lambda l: l**4*exp(-2*pi*l*y), [1, inf])
for a in [mpf('0.3'), mpf(1), mpf('2.5')]:
    lhs = quad(lambda y: wt(y)/(y**2+a**2), [0, 1, 5, inf])
    rhs = a**4*zeta(5, a) - 1/(2*a) - mpf(1)/4
    T = lambda l: (2*pi*l)**4/12*quad(lambda y: y**5*exp(-2*pi*l*y)/(y**2+a**2), [0, inf])
    R = lambda l: a**4/12*quad(lambda u: exp(-a*u)*u**5/(u**2+(2*pi*l)**2), [0, inf])
    g = lambda u: 1/(exp(u)-1) - 1/u + mpf(1)/2
    lap = a**4/24*quad(lambda u: exp(-a*u)*u**4*g(u), [0, 1, 10, inf])
    print('a =', a)
    print('  LHS', lhs); print('  RHS', rhs); print('  laplace', lap)
    print('  T_1,R_1', T(1), R(1)); print('  T_3,R_3', T(3), R(3))
    print('  sum R_l', nsum(R, [1, inf]))
    u = mpf('0.7'); print('  ML', g(u), nsum(lambda l: 2*u/(u**2+4*pi**2*l**2), [1, inf]))
