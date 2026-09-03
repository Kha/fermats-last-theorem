import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_NeronModelInfra_exists_opens_mul_extension_isOpenImmersion_lift_of_forall_nhds_translation_extension

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_opens_mul_extension_isOpenImmersion_lift_of_forall_nhds_translation_extension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (hL : ∀ (η : ↑(pullback f f)), (pullback.fst f f ≫ f).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ η → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = η) →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        IsOpenImmersion
          (pullback.lift (f := f) (g := f) (U.ι ≫ pullback.fst f f) τ.1
            ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U.ι ≫ pullback.fst f f ≫ f) τ) e).1 =
          pullback.map (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
              (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f)
                  ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (hR : ∀ (η : ↑(pullback f f)), (pullback.fst f f ≫ f).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ η → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = η) →
      ∃ (U : (pullback f f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst f f ≫ f) f),
        IsOpenImmersion
          (pullback.lift (f := f) (g := f) (U.ι ≫ pullback.fst f f) τ.1
            ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U.ι ≫ pullback.fst f f ≫ f) τ) e).1 =
          pullback.map (U.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
              (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f)
                  ⟨pullback.snd f f, pullback.condition.symm⟩) e)
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)).1) :
    ∃ (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f),
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ W) ∧
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
        p ∈ W) ∧
      (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
        pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
            (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
          (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (pullback.fst f f ≫ f)
                ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1 ∧
      IsOpenImmersion
        (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
          ((Category.assoc _ _ _).trans m.2.symm)) ∧
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
        p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
          ((Category.assoc _ _ _).trans m.2.symm)).base) ∧
      IsOpenImmersion
        (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
          (m.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
        p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
          (m.2.trans (by rw [Category.assoc, pullback.condition]))).base) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_opens_mul_extension_isOpenImmersion_lift_of_forall_nhds_translation_extension.solution
