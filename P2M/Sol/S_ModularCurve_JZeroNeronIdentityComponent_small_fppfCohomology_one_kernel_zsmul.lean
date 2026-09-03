import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Theorems.Thm_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections
import P2M.Util
namespace P2MW.S_ModularCurve_JZeroNeronIdentityComponent_small_fppfCohomology_one_kernel_zsmul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian ModularCurve

theorem solution
    (p : ℕ) [Fact p.Prime] (N : JZeroNeronIdentityComponent p)
    (𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom N.g)
    (he : ∀ {U V : specInt.Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s))
    (n : ℤ) :
    Small.{0} (fppfCohomology specInt (kernel (n • 𝟙 𝒢)) 1) := by
  haveI : ∀ U : specInt.Fppf, Small.{0} ((kernel (n • 𝟙 𝒢)).1.obj (op U)) := by
    intro U

    have hG : Small.{0} (𝒢.1.obj (op U)) := small_of_injective (e U).injective

    have hmono : Mono ((sheafToPresheaf _ _).map (kernel.ι (n • 𝟙 𝒢))) := inferInstance
    have hmono' : Mono (((sheafToPresheaf _ _).map (kernel.ι (n • 𝟙 𝒢))).app (op U)) := inferInstance
    have hinj : Function.Injective (((sheafToPresheaf _ _).map (kernel.ι (n • 𝟙 𝒢))).app (op U)) :=
      (AddCommGrpCat.mono_iff_injective _).mp hmono'
    exact @small_of_injective _ _ hG _ hinj
  exact AlgebraicGeometry.Scheme.small_fppfCohomology_one_specInt_of_small_sections _
