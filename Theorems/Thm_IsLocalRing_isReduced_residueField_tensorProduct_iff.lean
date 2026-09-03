import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isReduced_residueField_tensorProduct_iff

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem IsLocalRing.isReduced_residueField_tensorProduct_iff
    {A : Type*} [CommRing A] [IsLocalRing A]
    (R : Type*) [CommRing R] [Algebra A R] :
    IsReduced (ResidueField A ⊗[A] R) ↔ IsReduced (R ⧸ (maximalIdeal A).map (algebraMap A R)) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isReduced_residueField_tensorProduct_iff.solution
