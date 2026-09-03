import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing

set_option autoImplicit false

theorem ValuationSubring.eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing
    {K : Type} [Field K] (A : ValuationSubring K) [IsDiscreteValuationRing ↥A]
    (B : Subring K) (h : A.toSubring ≤ B) : B = A.toSubring ∨ B = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing.solution
