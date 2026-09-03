import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_eq_specMap_comp_of_formallyUnramified_of_forall_isIdempotentElem_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_eq_specMap_comp_of_formallyUnramified_of_forall_isIdempotentElem_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] {H : Scheme.{u}} (q : H ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType q] [FormallyUnramified q]
    (B : Type u) [CommRing B] [Nontrivial B] (ψ : k →+* B) (hB : ∀ b : B, IsIdempotentElem b → b = 0 ∨ b = 1)
    (x : Spec (CommRingCat.of B) ⟶ H) (hx : x ≫ q = Spec.map (CommRingCat.ofHom ψ)) :
    ∃ h : Spec (CommRingCat.of k) ⟶ H, h ≫ q = 𝟙 _ ∧ x = Spec.map (CommRingCat.ofHom ψ) ≫ h := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_eq_specMap_comp_of_formallyUnramified_of_forall_isIdempotentElem_of_isAlgClosed.solution
