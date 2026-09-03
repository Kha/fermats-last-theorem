import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import P2M.Util
namespace P2MW.S_ValuationSubring_residue_eq_residue_iff_valuation_sub_lt_one

set_option autoImplicit false

theorem solution {K : Type*} [Field K] (A : ValuationSubring K) {a b : K} (ha : a ∈ A) (hb : b ∈ A) :
    IsLocalRing.residue A ⟨a, ha⟩ = IsLocalRing.residue A ⟨b, hb⟩ ↔ A.valuation (a - b) < 1 := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
  rfl
