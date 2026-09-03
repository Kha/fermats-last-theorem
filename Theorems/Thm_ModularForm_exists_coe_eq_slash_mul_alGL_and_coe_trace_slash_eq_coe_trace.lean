import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_ModularForm_exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace
    (p M : ℕ) [NeZero p] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    [((CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ))).IsFiniteRelIndex
      (CohCarrier.GammaH (M / p) (H.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM))) : Subgroup (GL (Fin 2) ℝ))]
    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ)
    (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 M) (hσe : CohCarrier.gamma0Units M ⟨σ, hσ⟩ = e)
    (WQ : GL (Fin 2) ℝ) (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((M / p : ℕ) : ℝ), 0])
    {k : ℤ} (F : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ F' : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k,
      (⇑F' : UpperHalfPlane → ℂ) =
        (⇑F : UpperHalfPlane → ℂ) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) * Wd.alGL) ∧
      (⇑(ModularForm.trace
          (CohCarrier.GammaH (M / p) (H.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM))) : Subgroup (GL (Fin 2) ℝ)) F) :
          UpperHalfPlane → ℂ) ∣[k] WQ =
        ⇑(ModularForm.trace
          (CohCarrier.GammaH (M / p) (H.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM))) : Subgroup (GL (Fin 2) ℝ)) F') := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace.solution
