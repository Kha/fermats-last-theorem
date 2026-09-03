import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_iso_isoSpec_inv_comp_eq_of_specMap_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.TwoAffineOpenCover

universe u
theorem AlgebraicGeometry.exists_iso_isoSpec_inv_comp_eq_of_specMap_comp_eq
    {B B₁ : Type u} [CommRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁))
    (hI2 : RingHom.ker (algebraMap B B₁) * RingHom.ker (algebraMap B B₁) = ⊥)
    {X X₁ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (f₁ : X₁ ⟶ Spec (CommRingCat.of B₁)) (g : X₁ ⟶ X)
    (hg : IsPullback g f₁ f (Spec.map (CommRingCat.ofHom (algebraMap B B₁))))
    (U : X.Opens) (hU : IsAffineOpen U)
    (v : Spec (CommRingCat.of Γ(X, U)) ⟶ X)
    (hv : letI := algebraOfHom f U
      v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(X, U))))
    (hvu : letI := algebraOfHom f U
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U))))) ≫ hU.fromSpec
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(X, U))))) ≫ v) :
    ∃ α : (U : Scheme.{u}) ≅ U,
      hU.isoSpec.inv ≫ α.hom ≫ U.ι = v ∧
      α.hom ≫ U.ι ≫ f = U.ι ≫ f ∧
      (g ∣_ U) ≫ α.hom = g ∣_ U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_iso_isoSpec_inv_comp_eq_of_specMap_comp_eq.solution
