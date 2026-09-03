import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_isCompletionAlong_expand_eq

universe u v

open CategoryTheory

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_laurentChart_isCompletionAlong_expand_eq {R : Type u} [CommRing R] [IsLocalRing R] {X : AlgebraicGeometry.Scheme.{u}}
    (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ AlgebraicGeometry.Spec (.of R))
    [AlgebraicGeometry.SmoothOfRelativeDimension 1 c]
    {ι : Type v} (σ : ι → (AlgebraicGeometry.Spec (.of R) ⟶ X)) (h : 𝒱.IsSectional c σ) (i : ι)
    (t₀ : (𝒱.cover c).A0) (ht₀ : AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (h.comp_eq i) (h.range_subset i) t₀ = 0)
    (hgen : RingHom.ker (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (h.comp_eq i) (h.range_subset i)).toRingHom ≤
      Ideal.span {t₀} ⊔ RingHom.ker (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (h.comp_eq i) (h.range_subset i)).toRingHom ^ 2) :
    ∃ Λ : (𝒱.cover c).LaurentChart,
      Λ.IsCompletionAlong (𝒱.cover c).ρ0 (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (h.comp_eq i) (h.range_subset i)) ∧
        Λ.expand ((𝒱.cover c).ρ0 t₀) = HahnSeries.single 1 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_isCompletionAlong_expand_eq.solution
