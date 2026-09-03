import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_finite_flat_closedSubgroupScheme_of_torsion_genericFibre

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_finite_flat_closedSubgroupScheme_of_torsion_genericFibre
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} [IsSeparated f] (L : RelativeGroupLaw R f)
    (N : ℕ) [IsFinite (L.schemeKerStr N)]
    {BK : Scheme.{u}} {gK : BK ⟶ Spec (CommRingCat.of K)} [IsReduced BK] (LBK : RelativeGroupLaw K gK)
    (iK : SchemeHomOver gK (pullback.snd f (specGenericFibreInclusion R K)))
    (hci : IsClosedImmersion iK.1)
    (hiK : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t gK),
      NeronModelInfra.schemeHomOverComp (LBK.mul t x y) iK =
        (L.genericFibre K).mul t (NeronModelInfra.schemeHomOverComp x iK) (NeronModelInfra.schemeHomOverComp y iK))
    (hN : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t gK),
      (L.genericFibre K).nsmul t N (NeronModelInfra.schemeHomOverComp x iK) = (L.genericFibre K).one t) :
    ∃ (E : Scheme.{u}) (ι : E ⟶ J) (_ : IsClosedImmersion ι)
      (_ : IsFinite (ι ≫ f)) (_ : Flat (ι ≫ f)) (_ : LocallyOfFinitePresentation (ι ≫ f)),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), ∃ e : T ⟶ E, e ≫ ι = (L.one t).1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → (∃ e₂ : T ⟶ E, e₂ ≫ ι = y.1) →
          ∃ e : T ⟶ E, e ≫ ι = (L.mul t x y).1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        (∃ e₁ : T ⟶ E, e₁ ≫ ι = x.1) → ∃ e : T ⟶ E, e ≫ ι = (L.inv t x).1) ∧
      ∃ e : SchemeHomOver (pullback.snd (ι ≫ f) (specGenericFibreInclusion R K)) gK,
        IsIso e.1 ∧
        e.1 ≫ iK.1 =
          pullback.map (ι ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) (by rw [Category.comp_id, Category.id_comp]) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_finite_flat_closedSubgroupScheme_of_torsion_genericFibre.solution
