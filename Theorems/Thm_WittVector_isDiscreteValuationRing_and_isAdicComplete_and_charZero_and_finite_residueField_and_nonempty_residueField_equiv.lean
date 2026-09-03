import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import P2M.Util
import P2M.Sol.S_WittVector_isDiscreteValuationRing_and_isAdicComplete_and_charZero_and_finite_residueField_and_nonempty_residueField_equiv

theorem WittVector.isDiscreteValuationRing_and_isAdicComplete_and_charZero_and_finite_residueField_and_nonempty_residueField_equiv (p : ℕ) [Fact p.Prime]
    (k₀ : Type) [Field k₀] [Finite k₀] [CharP k₀ p] :
    IsDomain (WittVector p k₀) ∧ IsDiscreteValuationRing (WittVector p k₀) ∧
    IsAdicComplete (IsLocalRing.maximalIdeal (WittVector p k₀)) (WittVector p k₀) ∧
    CharZero (WittVector p k₀) ∧
    Finite (IsLocalRing.ResidueField (WittVector p k₀)) ∧
    ((p : WittVector p k₀) ∈ IsLocalRing.maximalIdeal (WittVector p k₀)) ∧
    Nonempty (IsLocalRing.ResidueField (WittVector p k₀) ≃+* k₀) := by p2m_exact_reverting @_root_.P2MW.S_WittVector_isDiscreteValuationRing_and_isAdicComplete_and_charZero_and_finite_residueField_and_nonempty_residueField_equiv.solution
