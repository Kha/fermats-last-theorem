import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_ptsN_eq_comp_of_mem_inertiaInvariants

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_ptsN_eq_comp_of_mem_inertiaInvariants
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension) :
    ∀ x : JZero (N₀ * p), x ∈ inertiaInvariants A (N₀ * p) →
      ∃ s : SchemeHomOver (𝟙 (shBase A)) F.gN, (F.ptsN x).1 = (barPt A ≫ shPt A) ≫ s.1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_ptsN_eq_comp_of_mem_inertiaInvariants.solution
