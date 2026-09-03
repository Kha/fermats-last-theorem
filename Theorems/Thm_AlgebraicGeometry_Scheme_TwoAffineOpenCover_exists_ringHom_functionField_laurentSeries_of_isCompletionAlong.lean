import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_ringHom_functionField_laurentSeries_of_isCompletionAlong

universe u v

open CategoryTheory

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_ringHom_functionField_laurentSeries_of_isCompletionAlong {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ AlgebraicGeometry.Spec (.of k))
    [AlgebraicGeometry.SmoothOfRelativeDimension 1 c] [Nonempty (↑(𝒱.U0 ⊓ 𝒱.U1) : AlgebraicGeometry.Scheme.{u})]
    (σ : AlgebraicGeometry.Spec (.of k) ⟶ X) (hσ : σ ≫ c = 𝟙 _) (hU : Set.range σ.base ⊆ (𝒱.U0 : Set X))
    (Λ : (𝒱.cover c).LaurentChart)
    (hΛ : Λ.IsCompletionAlong (𝒱.cover c).ρ0 (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom σ hσ hU))
    [Algebra k X.functionField] (v : AlgebraicCurve.Place k X.functionField)
    (hv : (algebraMap (X.presheaf.stalk (σ.base (IsLocalRing.closedPoint k))) X.functionField).range =
      v.toValuationSubring.toSubring) :
    ∃ Λ' : X.functionField →+* LaurentSeries k,
      (∀ y : (𝒱.cover c).A01, Λ' ((X.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom y) = Λ.expand y) ∧
        (∀ f : X.functionField, f ∈ v.toValuationSubring ↔ Λ' f ∈ (HahnSeries.ofPowerSeries ℤ k).range) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_ringHom_functionField_laurentSeries_of_isCompletionAlong.solution
