import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_le_and_le_toLocalSubring_of_toSubring_le

set_option autoImplicit false

universe u

open IsLocalRing

theorem ValuationSubring.exists_le_and_le_toLocalSubring_of_toSubring_le
    {K : Type u} [Field K] (O : ValuationSubring K) (R : LocalSubring K)
    (hRO : R.toSubring ≤ O.toSubring) :
    ∃ V : ValuationSubring K, V ≤ O ∧ R ≤ V.toLocalSubring := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_le_and_le_toLocalSubring_of_toSubring_le.solution
