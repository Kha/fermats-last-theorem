import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_weilRestriction_points_equiv

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem Algebra.exists_weilRestriction_points_equiv
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (H : Type u) [CommRing H] [Algebra B H] :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra A W),
      ∃ e : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) ≃ (H →ₐ[B] (B ⊗[A] T)),
        ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
          (f : W →ₐ[A] T), e T' (u.comp f) = (Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_weilRestriction_points_equiv.solution
