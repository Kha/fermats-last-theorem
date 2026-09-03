import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_hopfAlgebra_algEquiv_of_natural_mul

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem HopfAlgebra.exists_hopfAlgebra_algEquiv_of_natural_mul
    (A : Type u) [CommRing A] (W : Type u) [CommRing W] [Algebra A W]
    (mul : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) → (W →ₐ[A] T) → (W →ₐ[A] T))
    (one : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T))
    (inv : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) → (W →ₐ[A] T))
    (h_assoc : ∀ (T : Type u) [CommRing T] [Algebra A T] (f g h : W →ₐ[A] T),
      mul T (mul T f g) h = mul T f (mul T g h))
    (h_comm : ∀ (T : Type u) [CommRing T] [Algebra A T] (f g : W →ₐ[A] T), mul T f g = mul T g f)
    (h_one : ∀ (T : Type u) [CommRing T] [Algebra A T] (f : W →ₐ[A] T), mul T (one T) f = f)
    (h_inv : ∀ (T : Type u) [CommRing T] [Algebra A T] (f : W →ₐ[A] T), mul T (inv T f) f = one T)
    (h_nat_mul : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
      (f g : W →ₐ[A] T), u.comp (mul T f g) = mul T' (u.comp f) (u.comp g))
    (h_nat_one : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T'),
      u.comp (one T) = one T') :
    ∃ (W' : Type u) (_ : CommRing W') (_ : HopfAlgebra A W') (ψ : W' ≃ₐ[A] W),
      Coalgebra.IsCocomm A W' ∧
      ∀ (T : Type u) [CommRing T] [Algebra A T] (f g : W →ₐ[A] T),
        WithConv.toConv ((mul T f g).comp (ψ : W' →ₐ[A] W)) =
          WithConv.toConv (f.comp (ψ : W' →ₐ[A] W)) * WithConv.toConv (g.comp (ψ : W' →ₐ[A] W)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_hopfAlgebra_algEquiv_of_natural_mul.solution
