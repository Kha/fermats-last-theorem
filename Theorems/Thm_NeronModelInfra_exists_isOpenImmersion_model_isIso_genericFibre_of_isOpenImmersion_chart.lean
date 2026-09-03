import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_NeronModelInfra_exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart
attribute [-instance] NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (q : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion q.1] :
    ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ Spec (CommRingCat.of R)) (j : Y ⟶ Y') (hj : j ≫ f' = f)
      (e : SchemeHomOver (pullback.snd f' (specGenericFibreInclusion R K)) gK),
      IsOpenImmersion j ∧ IsSeparated f' ∧ LocallyOfFiniteType f' ∧ QuasiCompact f' ∧ IsIso e.1 ∧
      (∀ y' : Y', f'.base y' = IsLocalRing.closedPoint R → y' ∈ Set.range j.base) ∧
      schemeHomOverComp (genericFibreRestrict R K f' f ⟨j, hj⟩) e = q ∧
      (Smooth gK → Smooth f → Smooth f') := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_isOpenImmersion_model_isIso_genericFibre_of_isOpenImmersion_chart.solution
