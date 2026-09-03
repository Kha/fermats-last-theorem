import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_algHom_equiv_pi

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem Algebra.exists_algHom_equiv_pi
    (A : Type u) [CommRing A] (ι : Type) [Finite ι]
    (H : ι → Type u) [∀ i, CommRing (H i)] [∀ i, Algebra A (H i)]
    [∀ i, Module.Finite A (H i)] [∀ i, Module.Free A (H i)] :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra A W),
      Module.Finite A W ∧ Module.Free A W ∧
      ∃ e : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) ≃ (∀ i, H i →ₐ[A] T),
        ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
          (f : W →ₐ[A] T),
          e T' (u.comp f) = fun i => u.comp (e T f i) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_algHom_equiv_pi.solution
