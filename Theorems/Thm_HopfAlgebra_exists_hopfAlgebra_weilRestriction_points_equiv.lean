import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_hopfAlgebra_weilRestriction_points_equiv

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem HopfAlgebra.exists_hopfAlgebra_weilRestriction_points_equiv
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (H : Type u) [CommRing H] [HopfAlgebra B H] [Coalgebra.IsCocomm B H] :
    ∃ (W : Type u) (_ : CommRing W) (_ : HopfAlgebra A W),
      Coalgebra.IsCocomm A W ∧
      ∃ e : ∀ (T : Type u) [CommRing T] [Algebra A T],
          WithConv (W →ₐ[A] T) ≃ WithConv (H →ₐ[B] (B ⊗[A] T)),
        (∀ (T : Type u) [CommRing T] [Algebra A T] (f g : WithConv (W →ₐ[A] T)),
            e T (f * g) = e T f * e T g) ∧
        ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
          (f : WithConv (W →ₐ[A] T)),
          e T' (WithConv.toConv (u.comp f.ofConv))
            = WithConv.toConv ((Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f).ofConv) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_hopfAlgebra_weilRestriction_points_equiv.solution
