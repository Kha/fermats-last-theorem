import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_hecke_endomorphism

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_hecke_endomorphism
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension) :
    letI := heckeModuleBar (N₀ * p)
    ∀ t : HeckeAlg, ∃ φ : SchemeHomOver F.gN F.gN, ∀ x : JZero (N₀ * p), (F.ptsN (t • x)).1 = (F.ptsN x).1 ≫ φ.1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_hecke_endomorphism.solution
