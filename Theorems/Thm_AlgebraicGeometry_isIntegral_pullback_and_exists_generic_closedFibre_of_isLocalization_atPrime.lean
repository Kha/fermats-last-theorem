import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIntegral_pullback_and_exists_generic_closedFibre_of_isLocalization_atPrime
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
theorem AlgebraicGeometry.isIntegral_pullback_and_exists_generic_closedFibre_of_isLocalization_atPrime
    (p : ℕ) [Fact p.Prime]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    [(Ideal.span {(p : ℤ)}).IsPrime] [IsLocalization.AtPrime R (Ideal.span {(p : ℤ)})]
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [Smooth g] [QuasiCompact g]
    (hpre : ∀ s : Spec (CommRingCat.of ℤ), _root_.IsPreconnected (g.base ⁻¹' {s}))

    (e : Spec (CommRingCat.of ℤ) ⟶ G) (he : e ≫ g = 𝟙 (Spec (CommRingCat.of ℤ))) :
    ∃ (_ : IsIntegral (pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))))
      (η : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))),
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base η = IsLocalRing.closedPoint R ∧
      (∀ x : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))),
        (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base x = IsLocalRing.closedPoint R →
          η ⤳ x) ∧
      (∀ y : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))), y ⤳ η →
        (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base y = IsLocalRing.closedPoint R →
          y = η) ∧
      IsDiscreteValuationRing ((pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).presheaf.stalk η) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIntegral_pullback_and_exists_generic_closedFibre_of_isLocalization_atPrime.solution
