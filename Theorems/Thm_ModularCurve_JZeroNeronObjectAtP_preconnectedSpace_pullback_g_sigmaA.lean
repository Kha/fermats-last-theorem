import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_preconnectedSpace_pullback_g_sigmaA

set_option autoImplicit false

universe u

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  ModularCurve.JZeroNeronObjectAtP Topology

theorem ModularCurve.JZeroNeronObjectAtP.preconnectedSpace_pullback_g_sigmaA
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :
    PreconnectedSpace ↥(pullback O.g Λ.σA) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_preconnectedSpace_pullback_g_sigmaA.solution
