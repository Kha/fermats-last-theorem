import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_card_algHom_le_finrank_residueField_tensorProduct

set_option autoImplicit false

theorem Algebra.card_algHom_le_finrank_residueField_tensorProduct
    (R : Type*) [CommRing R] [IsLocalRing R]
    (B : Type*) [CommRing B] [Algebra R B] [Module.Finite R B]
    (Ω : Type*) [Field Ω] [Algebra R Ω] :
    Finite (B →ₐ[R] Ω) ∧
      Nat.card (B →ₐ[R] Ω) ≤
        Module.finrank (IsLocalRing.ResidueField R)
          (TensorProduct R (IsLocalRing.ResidueField R) B) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_card_algHom_le_finrank_residueField_tensorProduct.solution
