import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isSectional_pullback_and_isCompletionAlong_of_expand_map01_eq

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem exists_isSectional_pullback_and_isCompletionAlong_of_expand_map01_eq
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A]
    {ι : Type v} (σ : ι → (Spec (.of R) ⟶ X)) (hσ : 𝒱.IsSectional c σ)
    (Λ : ι → (𝒱.cover c).LaurentChart)
    (ΛA : ι → ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).LaurentChart)
    (hΛA : ∀ i y, (ΛA i).expand ((HomOver.baseChange 𝒱 c A).map01 y) = ((Λ i).expand y).map (algebraMap R A)) :
    ∃ (σA : ι → (Spec (.of A) ⟶ Limits.pullback c (specMap R A)))
      (hσA : (𝒱.pullback c A).IsSectional (pullback.snd c (specMap R A)) σA),
      (∀ i, σA i ≫ pullback.fst c (specMap R A) = specMap R A ≫ σ i) ∧
      (∀ i, (Λ i).IsCompletionAlong (𝒱.cover c).ρ0 (sectionAlgHom (σ i) (hσ.comp_eq i) (hσ.range_subset i)) →
        (ΛA i).IsCompletionAlong ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0
          (sectionAlgHom (σA i) (hσA.comp_eq i) (hσA.range_subset i))) ∧
      (∀ i, (Λ i).HasParameter (𝒱.cover c).ρ0 →
        (ΛA i).HasParameter ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isSectional_pullback_and_isCompletionAlong_of_expand_map01_eq.solution

end AlgebraicGeometry.Scheme.TwoAffineOpenCover
