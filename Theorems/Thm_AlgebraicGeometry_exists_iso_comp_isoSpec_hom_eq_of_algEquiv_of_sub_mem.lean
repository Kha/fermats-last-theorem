import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_iso_comp_isoSpec_hom_eq_of_algEquiv_of_sub_mem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.TwoAffineOpenCover

universe u
theorem AlgebraicGeometry.exists_iso_comp_isoSpec_hom_eq_of_algEquiv_of_sub_mem
    {B' B₁ : Type u} [CommRing B'] [CommRing B₁] [Algebra B' B₁]
    (hπ : Function.Surjective (algebraMap B' B₁))
    {X X₁ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B')) (f₁ : X₁ ⟶ Spec (CommRingCat.of B₁)) (g : X₁ ⟶ X)
    (hg : IsPullback g f₁ f (Spec.map (CommRingCat.ofHom (algebraMap B' B₁))))
    (U : X.Opens) (hU : IsAffineOpen U)
    (φ : letI := algebraOfHom f U
      Γ(X, U) ≃ₐ[B'] Γ(X, U))
    (hφ : letI := algebraOfHom f U
      ∀ x : Γ(X, U), φ x - x ∈ (RingHom.ker (algebraMap B' B₁)).map (algebraMap B' Γ(X, U))) :
    ∃ α : (U : Scheme.{u}) ≅ U,
      α.hom ≫ hU.isoSpec.hom = hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (letI := algebraOfHom f U; φ.toAlgHom.toRingHom)) ∧
      α.hom ≫ U.ι ≫ f = U.ι ≫ f ∧
      (g ∣_ U) ≫ α.hom = g ∣_ U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_iso_comp_isoSpec_hom_eq_of_algEquiv_of_sub_mem.solution
