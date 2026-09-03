import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import P2M.Util
import P2M.Sol.S_NeronModelInfra_exists_nhds_extension_chart_of_catchesIndexOnePoints
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.exists_nhds_extension_chart_of_catchesIndexOnePoints
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {AK : Scheme.{u}} {gK : AK ⟶ Spec (CommRingCat.of K)} [IsSeparated gK]
    (M : ModelFamily R K gK) (hM : ∀ i, LocallyOfFiniteType (M.str i))
    (hpts : M.CatchesIndexOnePoints)
    {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (ζ : Z) (hζ : z.base ζ = IsLocalRing.closedPoint R)
    (hmax : ∀ y : Z, y ⤳ ζ → z.base y = IsLocalRing.closedPoint R → y = ζ) :
    ∃ (i : M.ι) (U : Z.Opens) (_ : ζ ∈ U) (u : SchemeHomOver (U.ι ≫ z) (M.str i)),
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K (M.str i) (U.ι ≫ z) u) (M.chart i)).1 =
        pullback.map (U.ι ≫ z) (specGenericFibreInclusion R K) z (specGenericFibreInclusion R K) U.ι (𝟙 _)
          (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_nhds_extension_chart_of_catchesIndexOnePoints.solution
