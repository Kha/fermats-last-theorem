import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_NeronModelInfra_OmegaMinimalComponentData
import P2M.Util
import P2M.Sol.S_NeronModelInfra_exists_componentReading_data_of_smooth_of_forall_specializes
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite open AlgebraicGeometry hiding smoothOfRelativeDimension_of_smooth_of_genericFibre open NeronModelInfra hiding isIndexOneExtension_stalk_of_smooth_of_forall_specializes open GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_componentReading_data_of_smooth_of_forall_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤)) (hω : Scheme.Modules.IsFrameOn ω ⊤)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion e.1]
    (y : Y) (hy : f.base y = IsLocalRing.closedPoint R)
    (hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y) :
    ∃ (_ : IsDomain (Y.presheaf.stalk y)) (_ : IsDiscreteValuationRing (Y.presheaf.stalk y))
      (algebra : Algebra R (Y.presheaf.stalk y))
      (halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y))))
      (algebraK : Algebra K (FractionRing (Y.presheaf.stalk y)))
      (_ : IsScalarTower R K (FractionRing (Y.presheaf.stalk y)))
      (b : Module.Basis (Fin d) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄R]))
      (U : XK.Opens) (hU : IsAffineOpen U)
      (algebraU : Algebra Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))
      (_ : letI := gK.sectionsAlgebra U; IsScalarTower K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))
      (_ : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))) ≫ hU.fromSpec =
        (schemeHomOverComp
          (pointGenericFibre (K := K) (K' := FractionRing (Y.presheaf.stalk y))
            (⟨Y.fromSpecStalk y, halg⟩ :
              SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) f))
          e).1)
      (ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U)))
      (_ : gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω)
      (a : FractionRing (Y.presheaf.stalk y)),
      (letI := gK.sectionsAlgebra U;
        TopFormOrder.topFormMap K K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)) d ωU =
          a • TopFormOrder.topFormMap R K (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)) d
            (exteriorPower.ιMulti (Y.presheaf.stalk y) d b)) ∧
      a ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_componentReading_data_of_smooth_of_forall_specializes.solution
