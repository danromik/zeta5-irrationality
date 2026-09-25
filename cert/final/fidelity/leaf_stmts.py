# Compare the statements (text from 'theorem NAME' up to ':=') of the 19 blueprint leaves,
# and of eq_6_14/prop_6_3/configBound/eq_6_14_of_config, between commit 4dea216 and HEAD.
import subprocess,re
import os
ROOT=os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),"..","..",".."))
LEAVES="cauchy_cnd frullani_cauchy frullani_integrable gauss_pd swap_frullani rho_cross arcsine_smooth_err smooth_err_norm exists_nearest_cos integral_log_one_add_sq_div arcsine_pot intervalIntegrable_log_abs_sub_cos integral_log_abs_sub_cos_of_abs_le integral_log_abs_sub_cos_of_one_lt_abs pair_energy_ge kE_arc_comm kE_rhoM_expand Irho_double_sum integral_log_add_sq".split()
EXTRA="eq_6_14 prop_6_3 configBound eq_6_14_of_config ConfigBound kC kE rhoM arc arcsine Urho Uarc Vfield Vclosed".split()
def files(rev):
    out=subprocess.run(["git","-C",ROOT,"ls-tree","-r","--name-only",rev,"Zeta5/Sec6"],capture_output=True,text=True).stdout.split()
    return {f:subprocess.run(["git","-C",ROOT,"show",f"{rev}:{f}"],capture_output=True,text=True).stdout for f in out}
def stmts(fs):
    d={}
    for f,s in fs.items():
        for m in re.finditer(r"^(?:private )?(theorem|def|noncomputable def|abbrev) (\w+)(.*?)(:=)",s,re.S|re.M):
            d.setdefault(m.group(2),[]).append((f," ".join((m.group(3)).split())))
    return d
A=stmts(files("4dea216")); B=stmts(files("HEAD"))
bad=0
for n in LEAVES+EXTRA:
    a=A.get(n); b=B.get(n)
    same = a==b
    print(f"{n:45s} {'same' if same else 'DIFFERENT'}  {[x[0].split('/')[-1] for x in (b or [])]}")
    if not same: bad+=1; print("  OLD:",a,"\n  NEW:",b)
print("leaves found:",sum(1 for n in LEAVES if n in B),"/",len(LEAVES),"  differences:",bad)
# sorry in blueprint commit leaves
fsA=files("4dea216"); print("sorries at 4dea216:",sum(len(re.findall(r"\bsorry\b",re.sub(r"/-.*?-/|--.*","",s,flags=re.S))) for s in fsA.values()))
fsB=files("HEAD"); print("sorries at HEAD (Sec6, outside comments):",sum(len(re.findall(r"\bsorry\b",re.sub(r"/-.*?-/|--.*","",s,flags=re.S))) for s in fsB.values()))
