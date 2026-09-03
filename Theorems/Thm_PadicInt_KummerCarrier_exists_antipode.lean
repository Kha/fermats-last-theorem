import Mathlib
import Definitions.Def_PadicInt_KummerCarrier
import P2M.Util
import P2M.Sol.S_PadicInt_KummerCarrier_exists_antipode

open scoped TensorProduct in
open PadicInt.KummerCarrier in
theorem PadicInt.KummerCarrier.exists_antipode (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ) :
    ∃ S : Carrier p u →ₗ[ℤ_[p]] Carrier p u,
      (LinearMap.mul' ℤ_[p] (Carrier p u) ∘ₗ S.rTensor (Carrier p u) ∘ₗ (Δ p u).toLinearMap
        = Algebra.linearMap ℤ_[p] (Carrier p u) ∘ₗ (ε p u).toLinearMap) ∧
      (LinearMap.mul' ℤ_[p] (Carrier p u) ∘ₗ S.lTensor (Carrier p u) ∘ₗ (Δ p u).toLinearMap
        = Algebra.linearMap ℤ_[p] (Carrier p u) ∘ₗ (ε p u).toLinearMap) := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_KummerCarrier_exists_antipode.solution
