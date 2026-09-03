import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_valuation_sub_counit_lt_one_of_isClosedImmersion_of_specMap_comp_eq_zeroSection

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.valuation_sub_counit_lt_one_of_isClosedImmersion_of_specMap_comp_eq_zeroSection
    (A : Type) [CommRing A] [Algebra A (AlgebraicClosure ℚ)]

    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (zero : Spec (CommRingCat.of A) ⟶ X) (hzero : zero ≫ f = 𝟙 _)
    (B : Type) [CommRing B] [Bialgebra A B]
    (c : Spec (CommRingCat.of B) ⟶ X) [IsClosedImmersion c]
    (hc : c ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (hunit : Spec.map (CommRingCat.ofHom ((Bialgebra.counitAlgHom A B : B →ₐ[A] A) : B →+* A)) ≫ c = zero)

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (k : Type) [Field k] [Algebra A k] (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)
    (hπk : RingHom.ker πk = IsLocalRing.maximalIdeal ↥Pl)

    (g : B →ₐ[A] AlgebraicClosure ℚ) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) f)
    (hz : Spec.map (CommRingCat.ofHom ((g : B →ₐ[A] AlgebraicClosure ℚ) : B →+* AlgebraicClosure ℚ)) ≫ c =
      Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1)
    (hred : Spec.map (CommRingCat.ofHom πk) ≫ z.1 = Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ zero) :
    ∀ b : B, Pl.valuation (g b - algebraMap A (AlgebraicClosure ℚ) (Coalgebra.counit (R := A) b)) < 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_valuation_sub_counit_lt_one_of_isClosedImmersion_of_specMap_comp_eq_zeroSection.solution
