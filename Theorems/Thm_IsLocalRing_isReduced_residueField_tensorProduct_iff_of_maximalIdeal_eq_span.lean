import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isReduced_residueField_tensorProduct_iff_of_maximalIdeal_eq_span

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem IsLocalRing.isReduced_residueField_tensorProduct_iff_of_maximalIdeal_eq_span
    {A : Type*} [CommRing A] [IsLocalRing A] (a : A) (ha : maximalIdeal A = Ideal.span {a})
    (R : Type*) [CommRing R] [Algebra A R] :
    IsReduced (ResidueField A ⊗[A] R) ↔ IsReduced (R ⧸ Ideal.span {algebraMap A R a}) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isReduced_residueField_tensorProduct_iff_of_maximalIdeal_eq_span.solution
