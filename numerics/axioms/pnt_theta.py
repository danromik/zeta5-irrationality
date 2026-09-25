# Numerical sanity check of Zeta5.PNT.chebyshev_theta_asymptotic:
#   theta(x) / x -> 1, theta(x) = sum_{p <= x prime} log p  (Mathlib's Chebyshev.theta),
# and of the Riemann-sum consequence Zeta5.PNT.prime_riemann_sum for a discontinuous phi.
import math
N = 10**7
sieve = bytearray([1])*(N+1); sieve[0]=sieve[1]=0
for i in range(2,int(N**0.5)+1):
    if sieve[i]: sieve[i*i::i]=bytearray(len(sieve[i*i::i]))
primes=[i for i in range(N+1) if sieve[i]]
th=0.0; k=0
for x in [10**3,10**4,10**5,10**6,10**7]:
    while k<len(primes) and primes[k]<=x: th+=math.log(primes[k]); k+=1
    print(f"theta({x})/x = {th/x:.6f}")
# Riemann sum: a=0.2, b=1, phi = sign-like step + continuous part
phi=lambda y: (1.0 if y<0.5 else -2.0)+y*y
X=N; a,b=0.2,1.0
S=sum(phi(p/X)*math.log(p) for p in primes if a*X<p<=b*X)/X
I=(0.5-0.2)*1.0+(1-0.5)*(-2.0)+(1-0.008)/3
print("prime Riemann sum", S, "integral", I)
