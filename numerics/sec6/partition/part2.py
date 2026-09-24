from part import *
def Glo_loose(c,l,r):  # lower bound of G_c on [l,r], no monotonicity of G
    base=c*log(l+c*c)-2*c
    return base if l==0 else base+2*sqrt(l)*atan(c/sqrt(r))
def Ghi_loose(c,l,r):
    base=c*log(r+c*c)-2*c
    if l==0: return base+2*sqrt(r)*c*0+ (pi*sqrt(r))*c/c*0 + 2*sqrt(r)*(pi/2)  # atan<=pi/2
    return base+2*sqrt(r)*atan(c/sqrt(l))
def Vlo2(l,r): return 2*pi*sqrt(l)+Glo_loose(1,l,r)-6*Ghi_loose(alpha,l,r)
import part
part.Vlo=Vlo2
for delta in [mpf('2e-4')]:
    cs=part.cells(delta); print("loose: delta",delta,"cells",len(cs),"maxdepth",max(d for _,_,d in cs))
