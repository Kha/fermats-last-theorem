import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_hom_ext_of_field_of_apply_eq_of_surjective_zmod_residueField

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X : Scheme.{u}} (x : X) (q : ℕ) [Fact q.Prime]
    (π : ZMod q →+* X.residueField x) (hπ : Function.Surjective π)
    {K : Type u} [Field K] (f g : Spec (CommRingCat.of K) ⟶ X)
    (hf : f.base (IsLocalRing.closedPoint K) = x) (hg : g.base (IsLocalRing.closedPoint K) = x) :
    f = g := by
  subst hf

  have hsub : ∀ (φ ψ : X.residueField (f.base (IsLocalRing.closedPoint K)) ⟶ CommRingCat.of K), φ = ψ := by
    intro φ ψ
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    obtain ⟨a, rfl⟩ := hπ t
    have h1 : φ.hom.comp π = ψ.hom.comp π := Subsingleton.elim _ _
    exact RingHom.congr_fun h1 a
  apply (Scheme.SpecToEquivOfField K X).injective
  rw [Scheme.SpecToEquivOfField_eq_iff]
  exact ⟨hg.symm, hsub _ _⟩
