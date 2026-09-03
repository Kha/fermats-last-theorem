import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_residue_ne_zero_iff_valuation_eq_one

theorem ValuationSubring.residue_ne_zero_iff_valuation_eq_one {K : Type*} [Field K]
    (A : ValuationSubring K) {a : K} (ha : a ∈ A) :
    IsLocalRing.residue A ⟨a, ha⟩ ≠ 0 ↔ A.valuation a = 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_residue_ne_zero_iff_valuation_eq_one.solution
