import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_exists_inertiaInvariants_to_schemeHomOver_specGenericFibreInclusion_bijective

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_inertiaInvariants_to_schemeHomOver_specGenericFibreInclusion_bijective
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :
    ∃ yK : ↥(inertiaInvariants A (N₀ * p)) →
        SchemeHomOver (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) (RelativeGroupLaw.baseChangeStr Λ.shStr O.g),
      (∀ x, Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) ≫ (yK x).1 =
          (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1) ∧
      (∀ x x', yK (x + x') = (O.L.baseChange Λ.shStr).mul _ (yK x) (yK x')) ∧
      Function.Bijective yK := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_inertiaInvariants_to_schemeHomOver_specGenericFibreInclusion_bijective.solution
