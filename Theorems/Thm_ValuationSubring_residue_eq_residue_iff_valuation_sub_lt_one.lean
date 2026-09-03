import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_residue_eq_residue_iff_valuation_sub_lt_one

theorem ValuationSubring.residue_eq_residue_iff_valuation_sub_lt_one {K : Type*} [Field K]
    (A : ValuationSubring K) {a b : K} (ha : a ∈ A) (hb : b ∈ A) :
    IsLocalRing.residue A ⟨a, ha⟩ = IsLocalRing.residue A ⟨b, hb⟩ ↔ A.valuation (a - b) < 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_residue_eq_residue_iff_valuation_sub_lt_one.solution
