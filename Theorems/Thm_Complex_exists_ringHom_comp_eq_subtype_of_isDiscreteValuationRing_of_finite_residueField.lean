import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_exists_ringHom_comp_eq_subtype_of_isDiscreteValuationRing_of_finite_residueField

set_option autoImplicit false

theorem Complex.exists_ringHom_comp_eq_subtype_of_isDiscreteValuationRing_of_finite_residueField
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')] [CharZero O']
    (R : Subring ℂ) [Countable R] (iota : R →+* O') (hinj : Function.Injective iota) :
    ∃ e' : O' →+* ℂ, ∀ x : R, e' (iota x) = x := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_ringHom_comp_eq_subtype_of_isDiscreteValuationRing_of_finite_residueField.solution
