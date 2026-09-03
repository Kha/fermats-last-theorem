import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_NeronModelInfra_OmegaMinimalComponentData
import P2M.Util
import P2M.Sol.S_NeronModelInfra_MinimalComponentData_exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.MinimalComponentData.exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤))
    (D : MinimalComponentData R K gK d ω)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    (V : ∀ c : D.ι, ((D.C c).Y).Opens) (j : ∀ c : D.ι, SchemeHomOver ((V c).ι ≫ (D.C c).f) f)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsIso e.1]
    (hyV : ∀ c, (D.C c).y ∈ V c)
    (hVK : ∀ c (y' : ↥(D.C c).Y), (D.C c).f.base y' ≠ IsLocalRing.closedPoint R → y' ∈ V c)
    (hjopen : ∀ c, IsOpenImmersion (j c).1)
    (hjchart : ∀ c, (genericFibreRestrict R K f ((V c).ι ≫ (D.C c).f) (j c)).1 ≫ e.1 =
      (genericFibreRestrict R K (D.C c).f ((V c).ι ≫ (D.C c).f) ⟨(V c).ι, rfl⟩).1 ≫ (D.C c).e.1)
    (hcover : ∀ x : ↥X, ∃ c, x ∈ Set.range (j c).1.base)
    (ξ : ↥X) (hξ : f.base ξ = IsLocalRing.closedPoint R)
    (hξmax : ∀ y : ↥X, y ⤳ ξ → f.base y = IsLocalRing.closedPoint R → y = ξ)
    [Algebra R (X.presheaf.stalk ξ)]
    (halgX : X.fromSpecStalk ξ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ξ))))
    (F : Type u) [Field F] [Algebra (X.presheaf.stalk ξ) F] [Algebra R F] [Algebra K F]
    [IsScalarTower R (X.presheaf.stalk ξ) F] [IsScalarTower R K F]
    (hinj : Function.Injective (algebraMap (X.presheaf.stalk ξ) F)) :
    ∃ (c : D.ι) (φ : ((D.C c).Y.presheaf.stalk (D.C c).y) →+* (X.presheaf.stalk ξ))
      (_ : (j c).1.base ⟨(D.C c).y, hyV c⟩ = ξ)
      (_ : Function.Bijective φ) (_ : IsLocalHom φ)
      (_ : letI := (D.C c).algebra; φ.comp (algebraMap R ((D.C c).Y.presheaf.stalk (D.C c).y)) = algebraMap R (X.presheaf.stalk ξ))
      (algF : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F)
      (_ : letI : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) F := ((algebraMap (X.presheaf.stalk ξ) F).comp φ).toAlgebra
           IsScalarTower ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F)
      (_ : letI := (D.C c).algebraK; IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F),
      letI := gK.sectionsAlgebra (D.C c).U
      letI := (D.C c).algebraU
      letI : Algebra Γ(XK, (D.C c).U) F :=
        ((algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F).comp (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)))).toAlgebra
      Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, (D.C c).U) F)) ≫ (D.C c).hU.fromSpec =
        (NeronModelInfra.schemeHomOverComp
          (pointGenericFibre (K := K) (K' := F)
            (⟨X.fromSpecStalk ξ, halgX⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ξ)))) f))
          e).1 := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_MinimalComponentData_exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes.solution
