import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_ModularForm_exists_gammaH_coe_eq_of_forall_slash_eq

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_gammaH_coe_eq_of_forall_slash_eq
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    (g : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hg : ∀ γ ∈ CohCarrier.GammaH M H, (⇑g : UpperHalfPlane → ℂ) ∣[k] γ = ⇑g) :
    ∃ f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k,
      (⇑f : UpperHalfPlane → ℂ) = ⇑g := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_gammaH_coe_eq_of_forall_slash_eq.solution
