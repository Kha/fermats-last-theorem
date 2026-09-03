import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_exists_orientedCrossingChart_valuationSubring_of_chart

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing ModularCurve ModularCurve.XHDRLevel MvPolynomial
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_orientedCrossingChart_valuationSubring_of_chart
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})

    (ι : O →+* ↥A) (hι : ι.comp ρO = ρ) (hιinj : Function.Injective ι)
    (hιloc : ∀ o : O, ι o ∈ IsLocalRing.maximalIdeal ↥A ↔ o ∈ IsLocalRing.maximalIdeal O)
    (hιsurj : Function.Surjective (fun o : O => IsLocalRing.residue ↥A (ι o)))
    (hιfix : ∀ τ : ↥(A.decompositionSubgroup ℚ), τ ∈ A.inertiaSubgroup ℚ → ∀ o : O, τ • (ι o) = ι o)
    (htoκ : ((IsLocalRing.residue ↥A).comp ι).comp ρO = (IsLocalRing.residue ↥A).comp ρ)

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))

    (t : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (ht₁ : t ≫ pullback.snd _ _ = 𝟙 _)
    (ht₂ : t.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)) = (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n))
    (e : ℕ) (he : 1 ≤ e) (U₀ : (XO (ΓM M H) hj ρO).Opens) (hxU₀ : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO ((IsLocalRing.residue ↥A).comp ι) htoκ).base n ∈ U₀)
    (f₀ : (U₀ : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e))
    (hover₀ : f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))) = U₀.ι ≫ pullback.snd _ _)
    (hfib₀ : ∀ y : ↥(U₀ : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f₀.base y).asIdeal ∧ CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f₀.base y).asIdeal) ↔ U₀.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO ((IsLocalRing.residue ↥A).comp ι) htoκ).base n)
    (hpt₀ : ∀ y : ↥(U₀ : Scheme.{0}), U₀.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO ((IsLocalRing.residue ↥A).comp ι) htoκ).base n →
      (f₀.stalkMap y).hom.Flat ∧ Ideal.map (f₀.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧ IsIso (f₀.residueFieldMap y))
    (het₀ : ∀ y : ↥(U₀ : Scheme.{0}), U₀.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO ((IsLocalRing.residue ↥A).comp ι) htoκ).base n → ∃ V : (U₀ : Scheme.{0}).Opens, y ∈ V ∧ Etale (V.ι ≫ f₀))
    (hor₁ : ∀ y : ↥(U₀ : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f₀.base y).asIdeal → U₀.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO ((IsLocalRing.residue ↥A).comp ι) htoκ).base)
    (hor₂ : ∀ y : ↥(U₀ : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f₀.base y).asIdeal → U₀.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO ((IsLocalRing.residue ↥A).comp ι) htoκ).base)
    (hor₃ : ∀ y : ↥(U₀ : Scheme.{0}), U₀.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO ((IsLocalRing.residue ↥A).comp ι) htoκ).base → CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f₀.base y).asIdeal)
    (hor₄ : ∀ y : ↥(U₀ : Scheme.{0}), U₀.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO ((IsLocalRing.residue ↥A).comp ι) htoκ).base → CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f₀.base y).asIdeal)

    (bcA : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))
    (hbcA₁ : bcA ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbcA₂ : bcA ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) :
    ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
        (_ : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).base n ∈ U)
        (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : ↥A) ^ e)),

        f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥A (CrossingQuotient ↥A (((p : ℕ) : ↥A) ^ e)))) =
            U.ι ≫ pullback.snd _ _ ∧

        (∀ y : ↥(U : Scheme.{0}),
            (CrossingQuotient.U (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal ∧
              CrossingQuotient.V (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal) ↔
            U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).base n) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).base n →
            (f.stalkMap y).hom.Flat ∧
            Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
            IsIso (f.residueFieldMap y)) ∧

        (∃ W : (U : Scheme.{0}).Opens,
          (∃ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).base n ∧ y ∈ W) ∧
          AlgebraicGeometry.Etale (W.ι ≫ f)) ∧

        (∀ (τ : ↥(A.decompositionSubgroup ℚ)), τ ∈ A.inertiaSubgroup ℚ →
          ∀ (x' y' : ↥A) (hxy : x' * y' = algebraMap ↥A ↥A (((p : ℕ) : ↥A) ^ e))
            (hxy' : (MulSemiringAction.toRingHom _ (↥A) τ) x' * (MulSemiringAction.toRingHom _ (↥A) τ) y' =
              algebraMap ↥A ↥A (((p : ℕ) : ↥A) ^ e))
            (sU sU' : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})),
            sU ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ → sU' ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ →
            sU' ≫ U.ι ≫ pullback.fst _ _ =
              Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom _ (↥A) τ)) ≫ sU ≫ U.ι ≫ pullback.fst _ _ →
            sU ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e) x' y' hxy).toRingHom) →
            sU' ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e)
              ((MulSemiringAction.toRingHom _ (↥A) τ) x') ((MulSemiringAction.toRingHom _ (↥A) τ) y') hxy').toRingHom)) ∧

        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcA).base) ∧
        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcA).base) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcA).base →
            CrossingQuotient.V (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal) ∧
        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcA).base →
            CrossingQuotient.U (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_orientedCrossingChart_valuationSubring_of_chart.solution
