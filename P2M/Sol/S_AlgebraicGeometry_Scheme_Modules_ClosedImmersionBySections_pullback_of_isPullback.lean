import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {R R' : Type u} [CommRing R] [CommRing R'] (φ : R →+* R')
    {X X' : Scheme.{u}} {f : X ⟶ Spec (.of R)} {f' : X' ⟶ Spec (.of R')} (g : X' ⟶ X)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    {M : X.Modules} (hM : Scheme.Modules.ClosedImmersionBySections M f) :
    Scheme.Modules.ClosedImmersionBySections ((Scheme.Modules.pullback g).obj M) f' := by
  letI : Algebra R R' := φ.toAlgebra
  obtain ⟨N, 𝔓, h𝔓⟩ := hM
  have sq : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := hg
  obtain ⟨𝔓', -, -, hsq⟩ :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback sq 𝔓
  exact ⟨N, 𝔓', MorphismProperty.of_isPullback hsq h𝔓⟩
