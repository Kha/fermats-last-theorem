import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_extN_iff_closure_inter_preimage_closedPoint_nonempty

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.NeronExtension.extN_iff_closure_inter_preimage_closedPoint_nonempty
    {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
    {Λ : JZeroNeronObjectAtP.LevelData N₀ p A}
    {O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ} (F : O.NeronExtension) (x : JZero (N₀ * p)) :
    F.ExtN x ↔
      (closure {(F.ptsN x).1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))} ∩
        F.gN.base ⁻¹' {IsLocalRing.closedPoint ↥(shRing A)}).Nonempty := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_extN_iff_closure_inter_preimage_closedPoint_nonempty.solution
