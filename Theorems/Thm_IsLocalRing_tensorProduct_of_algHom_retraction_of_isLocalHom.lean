import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_tensorProduct_of_algHom_retraction_of_isLocalHom

open scoped TensorProduct

theorem IsLocalRing.tensorProduct_of_algHom_retraction_of_isLocalHom
    (R : Type*) [CommRing R] [IsLocalRing R]
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalRing A] [Module.Finite R A]
    (ε : A →ₐ[R] R)
    (O : Type*) [CommRing O] [Algebra R O] [IsLocalRing O] [IsLocalHom (algebraMap R O)] :
    IsLocalRing (O ⊗[R] A) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_tensorProduct_of_algHom_retraction_of_isLocalHom.solution
