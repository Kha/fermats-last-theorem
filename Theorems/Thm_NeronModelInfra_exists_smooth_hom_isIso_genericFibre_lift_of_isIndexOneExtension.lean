import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import P2M.Util
import P2M.Sol.S_NeronModelInfra_exists_smooth_hom_isIso_genericFibre_lift_of_isIndexOneExtension
attribute [-simp] AffineDilatation.coe_divElem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.exists_smooth_hom_isIso_genericFibre_lift_of_isIndexOneExtension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hK : Smooth (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃ (X' : Scheme.{u}) (u : X' ⟶ X),
      Smooth (u ≫ f) ∧ QuasiCompact (u ≫ f) ∧ IsSeparated u ∧
      IsIso (pullback.map (u ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) u
        (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)) ∧
      ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
        [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
          ∃ x' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (u ≫ f), x'.1 ≫ u = x.1 := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_smooth_hom_isIso_genericFibre_lift_of_isIndexOneExtension.solution
