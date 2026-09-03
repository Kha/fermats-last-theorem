import Mathlib
import P2M.Util
import P2M.Sol.S_AddCommGroup_moduleFinite_and_free_of_fg_saturation_of_ker_le_nsmul

set_option autoImplicit false

theorem AddCommGroup.moduleFinite_and_free_of_fg_saturation_of_ker_le_nsmul
    {R : Type*} [AddCommGroup R] [IsAddTorsionFree R]
    (hsat : ∀ M : AddSubgroup R, M.FG →
      ∃ M' : AddSubgroup R, M'.FG ∧ ∀ x : R, x ∈ M' ↔ ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ M)
    {G : Type*} [AddCommGroup G] [Finite G] (ρ : R →+ G) (n : ℕ) (hn : 1 < n)
    (hρ : ∀ x : R, ρ x = 0 → ∃ y : R, x = n • y) :
    Module.Finite ℤ R ∧ Module.Free ℤ R := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_moduleFinite_and_free_of_fg_saturation_of_ker_le_nsmul.solution
