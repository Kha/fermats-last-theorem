import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (m : ℕ) (hm : 0 < m) :
    (∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
        O.toricPoint m hm (χ * χ').ofConv = O.toricPoint m hm χ.ofConv + O.toricPoint m hm χ'.ofConv) ∧
    Function.Injective (O.toricPoint m hm) ∧
    (∀ x : JZero (N₀ * p), x ∈ O.toricPts m ↔ ∃ χ, O.toricPoint m hm χ = x) ∧
    Nat.card ↥(O.toricPts m) = m ^ O.toricRank := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard.solution
