import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_ModularForm_exists_gammaH_coe_eq_sum_of_forall_slash_eq

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_gammaH_coe_eq_sum_of_forall_slash_eq
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) [Fintype H] (k : ℤ)
    (F : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hF : ∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
      (⇑(F t) : UpperHalfPlane → ℂ) ∣[k] γ = ⇑(F (t * ((γ 1 1 : ℤ) : ZMod M)))) :
    ∃ V : ZMod M → ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ t : ZMod M, (⇑(V t) : UpperHalfPlane → ℂ) =
        ∑ h : H, (⇑(F (t * ((h : (ZMod M)ˣ) : ZMod M))) : UpperHalfPlane → ℂ)) ∧
      (∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(V t) : UpperHalfPlane → ℂ) ∣[k] γ = ⇑(V (t * ((γ 1 1 : ℤ) : ZMod M)))) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_gammaH_coe_eq_sum_of_forall_slash_eq.solution
