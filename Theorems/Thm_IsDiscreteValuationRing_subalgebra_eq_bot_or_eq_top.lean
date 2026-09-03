import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_subalgebra_eq_bot_or_eq_top

theorem IsDiscreteValuationRing.subalgebra_eq_bot_or_eq_top
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (S : Subalgebra R K) :
    S = ⊥ ∨ S = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_subalgebra_eq_bot_or_eq_top.solution
