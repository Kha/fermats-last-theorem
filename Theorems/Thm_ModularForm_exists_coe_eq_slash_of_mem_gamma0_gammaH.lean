import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_ModularForm_exists_coe_eq_slash_of_mem_gamma0_gammaH

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_coe_eq_slash_of_mem_gamma0_gammaH
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) {k : ℤ}
    (f : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ F : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k,
      (⇑F : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_coe_eq_slash_of_mem_gamma0_gammaH.solution
