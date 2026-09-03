import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_closedFibre_testCurves_of_integralPoints_through
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
theorem AlgebraicGeometry.exists_closedFibre_testCurves_of_integralPoints_through
    (p : ℕ) [Fact p.Prime]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    [(Ideal.span {(p : ℤ)}).IsPrime] [IsLocalization.AtPrime R (Ideal.span {(p : ℤ)})]
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [LocallyOfFiniteType g]

    (η : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))))
    (hη : (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base η = IsLocalRing.closedPoint R)

    (φη : SchemeHomOver (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))) (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))))
    (φK : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ⟶ pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))))
    (hφK : φK ≫ pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) = pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))))
    (θ : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ⟶ pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
    (hθ₁ : θ ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
    (hθ₂ : θ ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))))
    (hφ : φK ≫ θ = θ ≫ φη.1)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (hsupply : ∀ ζ : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ G,
      ζ ≫ g = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap ℤ ↥A))) →
      ∃ (s e : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g)
        (z zt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))),
        s.1.base (IsLocalRing.closedPoint ↥A) =
          ζ.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)) ∧
        z ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1 ∧
        zt ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = Spec.map (CommRingCat.ofHom A.subtype) ≫ e.1 ∧
        zt = z ≫ φη.1) :
    ∃ D : Set ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))),
      (∀ z ∈ D, (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base z = IsLocalRing.closedPoint R) ∧
      η ∈ closure D ∧
      (∀ z ∈ D, ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B)
        (c : Spec (CommRingCat.of B) ⟶ pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))),
        (c ≫ pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))).base (IsLocalRing.closedPoint B) = z ∧
        c.base ⟨⊥, Ideal.isPrime_bot⟩ ∈ Set.range
          (pullback.lift (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))))
            (φK ≫ pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))))
            (by rw [pullback.condition, Category.assoc, ← hφK, Category.assoc, pullback.condition])).base) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_closedFibre_testCurves_of_integralPoints_through.solution
