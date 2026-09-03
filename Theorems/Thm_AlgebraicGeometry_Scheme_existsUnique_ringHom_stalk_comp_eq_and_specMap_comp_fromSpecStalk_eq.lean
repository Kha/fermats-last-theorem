import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_existsUnique_ringHom_stalk_comp_eq_and_specMap_comp_fromSpecStalk_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry in

theorem AlgebraicGeometry.Scheme.existsUnique_ringHom_stalk_comp_eq_and_specMap_comp_fromSpecStalk_eq
    (X : Scheme.{u}) (x : X) (K : Type u) [Field K]
    (xbar : X.presheaf.stalk x →+* K)
    (hxbar : RingHom.ker xbar = IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (A : Type u) [CommRing A] [IsLocalRing A] (resA : A →+* K) (hresA : Function.Surjective resA) :
    (∀ ψ : X.presheaf.stalk x →+* A, resA.comp ψ = xbar →
        Spec.map (CommRingCat.ofHom resA) ≫ (Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x) =
          Spec.map (CommRingCat.ofHom xbar) ≫ X.fromSpecStalk x) ∧
    (∀ g : Spec (CommRingCat.of A) ⟶ X,
        Spec.map (CommRingCat.ofHom resA) ≫ g = Spec.map (CommRingCat.ofHom xbar) ≫ X.fromSpecStalk x →
        ∃! ψ : X.presheaf.stalk x →+* A, resA.comp ψ = xbar ∧
          Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x = g) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_existsUnique_ringHom_stalk_comp_eq_and_specMap_comp_fromSpecStalk_eq.solution
