import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_tensorProduct_of_moduleFinite_of_isAlgClosed_residueField

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem IsLocalRing.tensorProduct_of_moduleFinite_of_isAlgClosed_residueField
    (R : Type u) [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A] [IsLocalRing A]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] [IsLocalRing B] :
    IsLocalRing (A ⊗[R] B) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_tensorProduct_of_moduleFinite_of_isAlgClosed_residueField.solution
