import Mathlib
import P2M.Util
import P2M.Sol.S_Module_free_and_finrank_eq_of_finrank_residueField_tensor_eq_of_finrank_fractionRing_tensor_eq

set_option autoImplicit false

open scoped TensorProduct

theorem Module.free_and_finrank_eq_of_finrank_residueField_tensor_eq_of_finrank_fractionRing_tensor_eq
    {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    {C : Type*} [AddCommGroup C] [Module A C] [Module.Finite A C] (n : ℕ)
    (hκ : Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] C) = n)
    (hK : Module.finrank (FractionRing A) (FractionRing A ⊗[A] C) = n) :
    Module.Free A C ∧ Module.finrank A C = n := by p2m_exact_reverting @_root_.P2MW.S_Module_free_and_finrank_eq_of_finrank_residueField_tensor_eq_of_finrank_fractionRing_tensor_eq.solution
