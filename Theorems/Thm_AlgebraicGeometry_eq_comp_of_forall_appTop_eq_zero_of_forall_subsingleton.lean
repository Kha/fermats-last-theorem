import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton
    (k : Type u) [Field k] [IsAlgClosed k] {Z : Scheme.{u}} (q : Z ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType q] (S : Set Γ(Z, ⊤))
    (e : Spec (CommRingCat.of k) ⟶ Z)
    (hart : ∀ {T : Scheme.{u}} [Subsingleton ↥T] (t : T ⟶ Spec (CommRingCat.of k))
      [LocallyOfFiniteType t] (x : T ⟶ Z), x ≫ q = t → (∀ s ∈ S, x.appTop.hom s = 0) → x = t ≫ e)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : T ⟶ Z) (hx : x ≫ q = t)
    (hs : ∀ s ∈ S, x.appTop.hom s = 0) : x = t ≫ e := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton.solution
