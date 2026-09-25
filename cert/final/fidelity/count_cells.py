# Count the certified cells of Zeta5/Sec6/Num and check that the segments tile [0,2] contiguously.
import re,glob
import os
ROOT=os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),"..","..",".."))+"/"
tot=0; ends=[]
pat=re.compile(r"theorem (seg\w*) \(t : ℝ\) \(h1 : \((\d+) : ℝ\) / 10 \^ 12 ≤ t\) \(h2 : t ≤ \((\d+) : ℝ\) / 10 \^ 12\) :\s*2 \* Uclosed t - Vclosed t ≤ (-?\d+ / \d+) := by\s*have h := chain_sound \((-?\d+/\d+)\) \[([\d, ]*)\] (\d+) (\d+) \(by decide \+kernel\)")
for f in sorted(glob.glob(ROOT+"Zeta5/Sec6/Num/Seg*.lean"))+[ROOT+"Zeta5/Sec6/Num/Final.lean"]:
    s=open(f).read()
    n_thm=len(re.findall(r"chain_sound \(",s))
    found=0
    for m in pat.finditer(s):
        found+=1
        name,lo,hi,M,M2,L,a,b=m.groups()
        L=[int(x) for x in L.split(",")]
        assert M.replace(" ","")==M2,(name,M,M2)
        assert int(a)==int(lo) and L[-1]==int(hi),(name,)
        pts=[int(a),int(b)]+L
        assert all(x<y for x,y in zip(pts,pts[1:])),name
        ends.append((name,int(lo),int(hi),M2,len(pts)-1))
    assert found==n_thm,(f,found,n_thm)
main=sorted([e for e in ends if e[0]!="segB"],key=lambda e:e[1])
print("segments on [0,2]:",len(main)," cells:",sum(e[4] for e in main)," M:",set(e[3] for e in main))
print("range:",main[0][1],"..",main[-1][2]," (units 1e-12)")
assert main[0][1]==0 and main[-1][2]==2*10**12
assert all(main[i][2]==main[i+1][1] for i in range(len(main)-1)); print("contiguous tiling of [0,2]: OK")
B=[e for e in ends if e[0]=="segB"]; print("segB:",B)
