import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_iso_of_specMap_quotient_comp_eq_fromSpec

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Scheme.TwoAffineOpenCover

universe u
theorem AlgebraicGeometry.exists_iso_of_specMap_quotient_comp_eq_fromSpec
    {T' : Type u} [CommRing T'] (I : Ideal T') (hI2 : I * I = ⊥)
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T')) (U : Y.Opens) (hU : IsAffineOpen U)
    (v : Spec Γ(Y, U) ⟶ Y) (hv : v ≫ qY = hU.fromSpec ≫ qY)
    (hred : letI := algebraOfHom qY U
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ v =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.fromSpec) :
    ∃ τ : (U : Scheme.{u}) ≅ (U : Scheme.{u}),
      hU.isoSpec.inv ≫ τ.hom ≫ U.ι = v ∧
      τ.hom ≫ U.ι ≫ qY = U.ι ≫ qY ∧
      (∀ O : (U : Scheme.{u}).Opens, τ.hom ⁻¹ᵁ O = O) ∧
      (letI := algebraOfHom qY U
       Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.isoSpec.inv ≫ τ.hom =
         Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.isoSpec.inv) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_iso_of_specMap_quotient_comp_eq_fromSpec.solution
