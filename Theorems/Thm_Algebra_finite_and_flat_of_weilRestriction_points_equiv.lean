import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_finite_and_flat_of_weilRestriction_points_equiv

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem Algebra.finite_and_flat_of_weilRestriction_points_equiv
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    [Algebra.Etale A B]
    (H : Type u) [CommRing H] [Algebra B H] [Module.Finite B H] [Module.Free B H]
    (W : Type u) [CommRing W] [Algebra A W]
    (e : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) ≃ (H →ₐ[B] (B ⊗[A] T)))
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
      (f : W →ₐ[A] T), e T' (u.comp f) = (Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f)) :
    Module.Finite A W ∧ Module.Flat A W := by p2m_exact_reverting @_root_.P2MW.S_Algebra_finite_and_flat_of_weilRestriction_points_equiv.solution
