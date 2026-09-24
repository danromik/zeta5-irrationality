/-
Zeta5/Sec6/Final.lean  —  (6.14) and Proposition 6.3, assembled.  THIS FILE CONTAINS NO
`sorry`: `eq_6_14` is proved from the configuration bound `Sec6.configBound`
(`Sec6/Energy.lean`) and the Gram-integral argument `Sec6.Gram.eq_6_14_of_config`
(`Sec6/Gram.lean`).  The names and types of `Zeta5.RealBound.eq_6_14` and
`Zeta5.RealBound.prop_6_3` are exactly those they had in `Zeta5/RealBound.lean`.

## The route (the §6 blueprint)

```
eq_6_14  ⇐  Gram.eq_6_14_of_config         (6.10)–(6.13)          Gram.lean        (proved)
         ⇐  configBound ⇐ config_log      (6.9')                 Energy.lean      (proved)
              ⇐ eq_6_6_cauchy              (6.6')                 Energy.lean      (proved)
                 ⇐ cauchy_cnd             Lemma 6.2 for kC ε     CND.lean         LEAF
                     ⇐ frullani_cauchy, frullani_integrable       Frullani.lean    LEAVES
                     ⇐ gauss_pd                                   GaussPD.lean     LEAF
                     ⇐ swap_frullani                              Swap.lean        LEAF
                 ⇐ rho_cross              cross term             RhoCross.lean    LEAF
                     ⇐ arcsine_smooth_err                         SmoothArc.lean   LEAF
                         ⇐ smooth_err_norm                        SmoothErr.lean   LEAF
                             ⇐ exists_nearest_cos (+ cos_sub_cos_ge, proved)
                                                                  SmoothAux.lean   LEAF
                             ⇐ integral_log_one_add_sq_div        Antideriv.lean   LEAF
                         ⇐ arcsine_pot            (A.1)           ArcsinePot.lean  LEAF
                             ⇐ integral_log_abs_sub_cos           LogCos.lean      (proved)
                                 ⇐ intervalIntegrable_log_abs_sub_cos
                                                                  LogCosInt.lean   LEAF
                                 ⇐ integral_log_abs_sub_cos_of_abs_le
                                                                  LogCosOn.lean    LEAF
                                 ⇐ integral_log_abs_sub_cos_of_one_lt_abs
                                                                  LogCosOff.lean   LEAF
                 ⇐ rho_energy_ge          (A.2), energy of ρ     RhoEnergy.lean   (proved)
                     ⇐ pair_energy_ge  (uses arcsine_pot)         PairEnergy.lean  LEAF
                     ⇐ kE_arc_comm                                ArcComm.lean     LEAF
                     ⇐ kE_rhoM_expand                             Bilinear.lean    LEAF
                     ⇐ Irho_double_sum                            IrhoSum.lean     LEAF
              ⇐ eq_6_7_field               (6.7) for V of (6.1)   Potential.lean   (proved)
                 ⇐ Vfield_eq_Vclosed (A.5)                        Field.lean       (proved)
                     ⇐ integral_log_add_sq                        Field.lean       LEAF
                 ⇐ Num.eq_6_7_closed       (6.2), (6.7), (6.8)    Num/*.lean       (proved)
```

All files are in `Zeta5/Sec6/`.  Shared definitions are in `Defs.lean`; elementary facts about
the measures in `Measures.lean` (proved).  `Num/` is the kernel-checked certified partition
for (6.2)/(6.7) (1049 cells on `[0,2]`, 2 on `[2,4]`, an analytic tail for `t ≥ 4`; generated
by `numerics/sec6/gen_lean.py`).  Every leaf statement was tested numerically, with must-fail
controls: `numerics/sec6/check_leaves.py` (output `check_leaves.out`).

**Deviation from the paper (energy step).**  The paper regularises the configuration by
circles of radius `ε` in `ℂ` and applies Lemma 6.2 to the singular kernel `log|z − w|`.  We
keep the points as Dirac masses and regularise the kernel instead:
`kC ε x = ½ log(x² + ε²)` (`Sec6/Defs.lean`).  The zero-mass argument of Lemma 6.2 (Gaussian
positive definiteness + a Frullani representation) applies verbatim to `kC ε`, which is
bounded on compacts, so the diagonal, the log-integrability hypothesis and the dominated
convergence step of Lemma 6.2 disappear; every singular integral is one-dimensional
(in `θ`, for the arcsine measures `θ ↦ m + r cos θ`).  The constants close with a large
margin: (6.9') has `20h` where the paper has `(120+√2)h`, and `eq_6_14_of_config` accepts
`3h log K + 131h`.

**Deviation from the paper (Gram step)**: see `Sec6/Gram.lean` — the `1/h!` of (6.10) is kept
(it pays for one `h log K`), and `∫_0^∞(1+y)⁵e^{-y/K}dy ≤ 326K⁶` replaces the constant `652`.
-/
import Zeta5.Sec6.Energy

namespace Zeta5
namespace RealBound

open Real

/-- **(6.14)** (p. 20).  For `K ∈ 40ℤ_{>0}`,

`log Δ_K(ζ(5)) ≤ 2h(h + 6N − K) log K + (λM₀ − I(ρ))K² + 18h log K + 160h`.

Stated verbatim as printed; nothing is weakened.  Proved from the configuration bound
`Sec6.configBound` (the paper's (6.9) with `20h` in place of `(120+√2)h`) by the Gram-integral
argument `Sec6.Gram.eq_6_14_of_config` ((6.10)–(6.13)), which accepts any configuration
constant `A ≤ (λM₀ − I(ρ))K² + 3h log K + 131h`. -/
theorem eq_6_14 (n : ℕ) (hn : 0 < n) (hΔpos : 0 < evalZeta5 (Delta n)) :
    Real.log (evalZeta5 (Delta n))
      ≤ 2 * (h n : ℝ) * ((h n : ℝ) + 6 * (N n : ℝ) - (K n : ℝ)) * Real.log (K n : ℝ)
        + ((lam : ℝ) * M0 - Irho) * (K n : ℝ) ^ 2
        + 18 * (h n : ℝ) * Real.log (K n : ℝ) + 160 * (h n : ℝ) := by
  refine Sec6.Gram.eq_6_14_of_config n hn hΔpos _ (Sec6.configBound n hn) ?_
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hK : ((K n : ℕ) : ℝ) = 40 * (n : ℝ) := by simp only [K]; push_cast; ring
  have hlogK : 0 ≤ Real.log (K n : ℝ) := Real.log_nonneg (by rw [hK]; linarith)
  have hh : (0 : ℝ) ≤ (h n : ℝ) := by positivity
  nlinarith [mul_nonneg hh hlogK]

/-- **Proposition 6.3**, (6.16) (p. 20): `log F_K(ζ(5)) ≤ Ū K² + 24K log K + 200K`.

`hΔpos` is the positivity `0 < Δ_K(ζ(5))`, which the paper gets from Proposition 2.2;
in the project it is `Zeta5.delta_pos`, so `Zeta5.Interface.prop_6_3` is discharged by
`Zeta5.RealBound.prop_6_3 n hn (Zeta5.delta_pos n)`. -/
theorem prop_6_3 (n : ℕ) (hn : 0 < n) (hΔpos : 0 < evalZeta5 (Delta n)) :
    Real.log (evalZeta5 (F n))
      ≤ (Ubar : ℝ) * (K n : ℝ) ^ 2 + 24 * (K n : ℝ) * Real.log (K n : ℝ)
        + 200 * (K n : ℝ) :=
  prop_6_3_of n hn hΔpos (eq_6_14 n hn hΔpos) (eq_6_15 n hn)

end RealBound
end Zeta5
