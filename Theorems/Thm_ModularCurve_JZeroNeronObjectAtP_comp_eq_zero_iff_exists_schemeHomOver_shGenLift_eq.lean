import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_comp_eq_zero_iff_exists_schemeHomOver_shGenLift_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.comp_eq_zero_iff_exists_schemeHomOver_shGenLift_eq
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (x : ↥(inertiaInvariants A (N₀ * p))) :
    O.comp x = 0 ↔
      ∃ s : SchemeHomOver (𝟙 (shBase A)) (RelativeGroupLaw.baseChangeStr Λ.shStr O.g),
        (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1 = (barPt A ≫ shPt A) ≫ s.1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_comp_eq_zero_iff_exists_schemeHomOver_shGenLift_eq.solution
