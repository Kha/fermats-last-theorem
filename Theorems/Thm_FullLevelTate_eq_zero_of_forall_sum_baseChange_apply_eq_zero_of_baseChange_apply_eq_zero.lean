import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_JZeroTateModule
import P2M.Util
import P2M.Sol.S_FullLevelTate_eq_zero_of_forall_sum_baseChange_apply_eq_zero_of_baseChange_apply_eq_zero

set_option autoImplicit false

open scoped TensorProduct

theorem FullLevelTate.eq_zero_of_forall_sum_baseChange_apply_eq_zero_of_baseChange_apply_eq_zero
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime] (X : Type) [AddCommGroup X] [Module ℚ_[lam] X]
    (sp₀ : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M') →ₗ[ℚ_[lam]] X)
    (K : Type) [CommRing K] [Algebra ℚ_[lam] K] :
    (∀ v : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M'),
        (∀ g : CuspidalType.GL2 q,
          (∑ t : ZMod q, (ModularCurve.FullLevel.tateGL2 q M' lam (CuspidalType.unipotent q t)).baseChange ℚ_[lam] *
              (ModularCurve.FullLevel.tateGL2 q M' lam g).baseChange ℚ_[lam]) v = 0) →
        sp₀ v = 0 → v = 0) →
      ∀ v' : K ⊗[ℚ_[lam]] ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M'),
        (∀ g : CuspidalType.GL2 q,
          (∑ t : ZMod q,
            ((ModularCurve.FullLevel.tateGL2 q M' lam (CuspidalType.unipotent q t)).baseChange ℚ_[lam]).baseChange K *
              ((ModularCurve.FullLevel.tateGL2 q M' lam g).baseChange ℚ_[lam]).baseChange K) v' = 0) →
          sp₀.baseChange K v' = 0 → v' = 0 := by p2m_exact_reverting @_root_.P2MW.S_FullLevelTate_eq_zero_of_forall_sum_baseChange_apply_eq_zero_of_baseChange_apply_eq_zero.solution
