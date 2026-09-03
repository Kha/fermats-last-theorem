import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Flat_of_forall_flat_quotient_pow_tensor_of_map_le_jacobson

set_option autoImplicit false

open scoped TensorProduct

theorem Module.Flat.of_forall_flat_quotient_pow_tensor_of_map_le_jacobson
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B]
    (I : Ideal A) (hI : I.map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson)
    (h : ∀ n : ℕ, Module.Flat (A ⧸ I ^ n) ((A ⧸ I ^ n) ⊗[A] B)) :
    Module.Flat A B := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_of_forall_flat_quotient_pow_tensor_of_map_le_jacobson.solution
