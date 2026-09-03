import Mathlib
import P2M.Util
import P2M.Sol.S_Module_free_and_finrank_eq_of_finrank_eq_mul_of_finrank_residueField_tensor_le

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem Module.free_and_finrank_eq_of_finrank_eq_mul_of_finrank_residueField_tensor_le
    {𝒪 A M : Type*} [CommRing 𝒪] [IsDomain 𝒪] [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    [Module.Finite 𝒪 A] [Module.Free 𝒪 A]
    [AddCommGroup M] [Module 𝒪 M] [Module A M] [IsScalarTower 𝒪 A M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (d : ℕ) (hd : Module.finrank (ResidueField A) (ResidueField A ⊗[A] M) ≤ d)
    (hM : Module.finrank 𝒪 M = d * Module.finrank 𝒪 A) :
    Module.Free A M ∧ Module.finrank A M = d := by p2m_exact_reverting @_root_.P2MW.S_Module_free_and_finrank_eq_of_finrank_eq_mul_of_finrank_residueField_tensor_le.solution
