import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_isIso_genericFibreRestrict_openImm

set_option autoImplicit false

open CategoryTheory NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP open AlgebraicGeometry hiding isIso_of_isOpenImmersion_of_forall_exists_comp_eq_of_isAlgClosed

theorem ModularCurve.JZeroNeronObjectAtP.NeronExtension.isIso_genericFibreRestrict_openImm
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension) :
    IsIso (NeronModelInfra.genericFibreRestrict ↥(shRing A) ↥(invField A) F.gN
      (RelativeGroupLaw.baseChangeStr Λ.shStr O.g) F.openImm).1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_isIso_genericFibreRestrict_openImm.solution
