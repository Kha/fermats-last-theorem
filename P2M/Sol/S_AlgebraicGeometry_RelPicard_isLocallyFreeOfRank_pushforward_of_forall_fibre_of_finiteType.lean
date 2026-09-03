import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_finite_H0_H1_sectionsOf
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve"

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (F : (pullback c (Spec.map (CommRingCat.ofHom (algebraMap R A)))).Modules)
    (hF : Scheme.Modules.IsInvertible F) (n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A))
      (𝒲 : (pullback (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R A)))) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A))) s)
        (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A))) s F)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A))) s)
          (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A))) s F)).H0 = n) :
    Scheme.Modules.IsLocallyFreeOfRank n
      ((Scheme.Modules.pushforward (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R A))))).obj F) := by

  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  haveI : Flat (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R A)))) := inferInstance

  obtain ⟨𝔉, -⟩ := h𝔉 0
  obtain ⟨𝔉A, -, -, -, -⟩ := 𝔉.exists_baseChange A
  have hfin := 𝔉A.finite_H0_H1_sectionsOf F hF.exists_trivialization

  exact Scheme.Modules.isLocallyFreeOfRank_pushforward_of_twoAffineOpenCover
    (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R A)))) 𝔉A.twoAffineOpenCover F
    hF.exists_trivialization hfin n
    (fun K _ _ => hfib K (Scheme.TwoAffineOpenCover.specMap A K)
      (𝔉A.twoAffineOpenCover.pullback (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R A)))) K))
