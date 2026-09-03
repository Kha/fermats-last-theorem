import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_hom_ext_of_field_of_apply_eq_of_surjective_zmod_residueField

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.hom_ext_of_field_of_apply_eq_of_surjective_zmod_residueField
    {X : Scheme.{u}} (x : X) (q : ℕ) [Fact q.Prime]
    (π : ZMod q →+* X.residueField x) (hπ : Function.Surjective π)
    {K : Type u} [Field K] (f g : Spec (CommRingCat.of K) ⟶ X)
    (hf : f.base (IsLocalRing.closedPoint K) = x) (hg : g.base (IsLocalRing.closedPoint K) = x) :
    f = g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_hom_ext_of_field_of_apply_eq_of_surjective_zmod_residueField.solution
