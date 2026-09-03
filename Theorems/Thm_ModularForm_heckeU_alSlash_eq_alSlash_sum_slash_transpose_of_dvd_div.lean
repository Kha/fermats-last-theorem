import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice
import P2M.Util
import P2M.Sol.S_ModularForm_heckeU_alSlash_eq_alSlash_sum_slash_transpose_of_dvd_div

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.heckeU_alSlash_eq_alSlash_sum_slash_transpose_of_dvd_div
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M (M / p))
    (q' : ℕ) (hq' : q'.Prime) (hq'Q : q' ∣ M / p) (k : ℤ)
    (f : UpperHalfPlane → ℂ)
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) :
    ModularForm.heckeU k q' (ModularForm.alSlash W k f) =
      ModularForm.alSlash W k
        (∑ j ∈ Finset.range q',
          f ∣[k] (ModularForm.heckeDiagMatrix q' *
            (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T ^ (-((M * j : ℕ) : ℤ)) * ModularGroup.S⁻¹) :
              GL (Fin 2) ℝ))) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_heckeU_alSlash_eq_alSlash_sum_slash_transpose_of_dvd_div.solution
