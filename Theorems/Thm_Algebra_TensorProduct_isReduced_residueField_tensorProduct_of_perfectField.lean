import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_isReduced_residueField_tensorProduct_of_perfectField

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem Algebra.TensorProduct.isReduced_residueField_tensorProduct_of_perfectField
    (A' : Type*) [CommRing A'] [IsLocalRing A'] [PerfectField (ResidueField A')]
    (A : Type*) [CommRing A] [IsLocalRing A] [Algebra A' A] [IsLocalHom (algebraMap A' A)]
    (C : Type*) [CommRing C] [Algebra A' C]
    (h : IsReduced (ResidueField A' ⊗[A'] C)) :
    IsReduced (ResidueField A ⊗[A'] C) ∧ IsReduced (ResidueField A ⊗[A] (A ⊗[A'] C)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_isReduced_residueField_tensorProduct_of_perfectField.solution
