import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import P2M.Util
namespace P2MW.S_ValuationSubring_residue_ne_zero_iff_valuation_eq_one

set_option autoImplicit false

theorem solution {K : Type*} [Field K] (A : ValuationSubring K) {a : K} (ha : a ∈ A) :
    IsLocalRing.residue A ⟨a, ha⟩ ≠ 0 ↔ A.valuation a = 1 := by
  rw [IsLocalRing.residue_ne_zero_iff_isUnit, A.valuation_eq_one_iff]
