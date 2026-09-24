from data import *
import mpmath
mp.dps=30
pts=sorted(set([mpf(i)/20000 for i in range(40001)]+a+b))
vals=[(F(t),t) for t in pts]
m=max(vals); print("max F on grid",m, "margin",M0-m[0])
# margins by region
import math
for lo,hi in [(0,a[15]),(a[15],a[0]),(a[0],b[0]),(b[0],b[15]),(b[15],2)]:
    v=[x for x in vals if lo<=x[1]<=hi]; mm=max(v); print(float(lo),float(hi),"max",mm[0],"at",mm[1],"margin",float(M0-mm[0]))
print("F(0)",F(mpf(0)),"F(2)",F(mpf(2)))
