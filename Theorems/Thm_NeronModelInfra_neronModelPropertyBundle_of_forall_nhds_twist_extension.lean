import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_NeronModelInfra_neronModelPropertyBundle_of_forall_nhds_twist_extension
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.neronModelPropertyBundle_of_forall_nhds_twist_extension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
    [Smooth g] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g)
    (htw : ∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
      (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K))
        (pullback.snd g (specGenericFibreInclusion R K)))
      (η : ↑(pullback z g)), (pullback.fst z g ≫ z).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback z g), y ⤳ η → (pullback.fst z g ≫ z).base y = IsLocalRing.closedPoint R → y = η) →
      ∃ (U : (pullback z g).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z g ≫ z) g),
        (genericFibreRestrict R K g (U.ι ≫ pullback.fst z g ≫ z) τ).1 =
          pullback.map (U.ι ≫ pullback.fst z g ≫ z) (specGenericFibreInclusion R K)
              (pullback.fst z g ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            ((LB.genericFibre K).mul (pullback.snd (pullback.fst z g ≫ z) (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K z (pullback.fst z g ≫ z) ⟨pullback.fst z g, rfl⟩) uK)
              (genericFibreRestrict R K g (pullback.fst z g ≫ z)
                ⟨pullback.snd z g, pullback.condition.symm⟩)).1) :
    NeronModelPropertyBundle R K g := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_neronModelPropertyBundle_of_forall_nhds_twist_extension.solution
