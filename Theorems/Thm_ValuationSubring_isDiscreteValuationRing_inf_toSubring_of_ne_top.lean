import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_isDiscreteValuationRing_inf_toSubring_of_ne_top

set_option autoImplicit false

theorem ValuationSubring.isDiscreteValuationRing_inf_toSubring_of_ne_top
    (O : ValuationSubring (AlgebraicClosure ℚ)) (hO : O ≠ ⊤)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] :
    IsDiscreteValuationRing ↥(O.toSubring ⊓ K.toSubring) ∧
      ∀ x : AlgebraicClosure ℚ, x ∈ K →
        ∃ a b : AlgebraicClosure ℚ, a ∈ O.toSubring ⊓ K.toSubring ∧ b ∈ O.toSubring ⊓ K.toSubring ∧
          b ≠ 0 ∧ x * b = a := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isDiscreteValuationRing_inf_toSubring_of_ne_top.solution
