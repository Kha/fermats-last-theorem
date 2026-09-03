import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
import Theorems.Thm_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section_apply_eq_X
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_formallySmooth_cover_A0
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_cotangent_sectionAlgHom
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_isCompletionAlong_of_powerSeries
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_isCompletionAlong_expand_eq

universe u v

open CategoryTheory

theorem solution {R : Type u} [CommRing R] [IsLocalRing R] {X : AlgebraicGeometry.Scheme.{u}}
    (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ AlgebraicGeometry.Spec (.of R))
    [AlgebraicGeometry.SmoothOfRelativeDimension 1 c]
    {ι : Type v} (σ : ι → (AlgebraicGeometry.Spec (.of R) ⟶ X)) (h : 𝒱.IsSectional c σ) (i : ι)
    (t₀ : (𝒱.cover c).A0) (ht₀ : AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (h.comp_eq i) (h.range_subset i) t₀ = 0)
    (hgen : RingHom.ker (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (h.comp_eq i) (h.range_subset i)).toRingHom ≤
      Ideal.span {t₀} ⊔ RingHom.ker (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (h.comp_eq i) (h.range_subset i)).toRingHom ^ 2) :
    ∃ Λ : (𝒱.cover c).LaurentChart,
      Λ.IsCompletionAlong (𝒱.cover c).ρ0 (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (h.comp_eq i) (h.range_subset i)) ∧
        Λ.expand ((𝒱.cover c).ρ0 t₀) = HahnSeries.single 1 1 := by
  haveI : AlgebraicGeometry.Smooth c := AlgebraicGeometry.SmoothOfRelativeDimension.smooth 1 c
  haveI : Algebra.FormallySmooth R (𝒱.cover c).A0 :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.formallySmooth_cover_A0 𝒱 c
  obtain ⟨hfree, hrank⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.free_cotangent_sectionAlgHom (𝒱 := 𝒱) (c := c)
      (σ i) (h.comp_eq i) (h.range_subset i)
  haveI := hfree
  obtain ⟨θ, h1, h2, h3, ht⟩ := Algebra.FormallySmooth.exists_powerSeries_expansion_along_section_apply_eq_X
    (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (h.comp_eq i) (h.range_subset i)) hrank t₀ ht₀ hgen
  obtain ⟨Λ, hΛθ, hΛ⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_laurentChart_isCompletionAlong_of_powerSeries
      𝒱 c σ h i θ h1 h2 h3
  exact ⟨Λ, hΛ, by rw [hΛθ, ht, HahnSeries.ofPowerSeries_X]⟩
