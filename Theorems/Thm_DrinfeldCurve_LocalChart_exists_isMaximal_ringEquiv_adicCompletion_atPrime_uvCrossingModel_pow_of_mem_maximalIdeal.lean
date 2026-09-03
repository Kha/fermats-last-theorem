import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_exists_isMaximal_ringEquiv_adicCompletion_atPrime_uvCrossingModel_pow_of_mem_maximalIdeal
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

noncomputable section

open MvPowerSeries open IsLocalRing hiding exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_pow_mul_unit open DrinfeldCurve DrinfeldCurve.LocalChart ModularCurve ModularCurve.UVCrossingModel

theorem DrinfeldCurve.LocalChart.exists_isMaximal_ringEquiv_adicCompletion_atPrime_uvCrossingModel_pow_of_mem_maximalIdeal
    (q : ℕ) [Fact q.Prime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    (π : O) (hπ : maximalIdeal O = Ideal.span {π})
    (ϖ : O) (hϖ : ϖ ∈ maximalIdeal O) (hϖ0 : ϖ ≠ 0)
    (m : ℕ) (hm : 1 ≤ m) (ε : Oˣ) (hϖπ : ϖ = π ^ m * (ε : O))
    (pr : ChartPresentation q O ϖ)
    (hnzd : Ideal.Quotient.mk (Ideal.span {pr.rel}) (X 0) ∈ nonZeroDivisors pr.Ring)
    (hqO : (q : O) ∈ maximalIdeal O) (a : O) (ha : a ^ q - a ∈ maximalIdeal O) :
    let S := pr.Ring
    let mkS : MvPowerSeries (Fin 2) O →+* S := Ideal.Quotient.mk _
    let L := Localization.Away (mkS (X 0))
    let ι₀ : O →+* L := (algebraMap S L).comp (mkS.comp (C (σ := Fin 2) (R := O)))
    let y : L := algebraMap S L (mkS (X 0))
    let x : L := ι₀ ϖ * IsLocalization.Away.invSelf (S := L) (mkS (X 0))
    let w : L := algebraMap S L (mkS (X 1)) * IsLocalization.Away.invSelf (S := L) (mkS (X 0))
    let R₀ : Subring L := Subring.closure (Set.range (algebraMap S L) ∪ {x, w})
    ∃ (hι₀ : ∀ o : O, ι₀ o ∈ R₀) (hx : x ∈ R₀) (hy : y ∈ R₀) (hw : w ∈ R₀)
      (𝔪a : Ideal ↥R₀) (_ : 𝔪a.IsMaximal),
      𝔪a = Ideal.span {⟨ι₀ π, hι₀ π⟩, ⟨y, hy⟩, ⟨x, hx⟩, ⟨w, hw⟩ - ⟨ι₀ a, hι₀ a⟩} ∧
      x * y = ι₀ ϖ ∧
      IsNoetherianRing (Localization.AtPrime 𝔪a) ∧
      maximalIdeal (Localization.AtPrime 𝔪a) =
        Ideal.span {algebraMap (↥R₀) (Localization.AtPrime 𝔪a) ⟨ι₀ π, hι₀ π⟩,
          algebraMap (↥R₀) (Localization.AtPrime 𝔪a) ⟨x, hx⟩,
          algebraMap (↥R₀) (Localization.AtPrime 𝔪a) ⟨y, hy⟩} ∧
      algebraMap (↥R₀) (Localization.AtPrime 𝔪a) (⟨w, hw⟩ - ⟨ι₀ a, hι₀ a⟩) ∈ maximalIdeal (Localization.AtPrime 𝔪a) ∧

      (∀ g : Localization.AtPrime 𝔪a, ∃ o : O,
        g - algebraMap (↥R₀) (Localization.AtPrime 𝔪a) ⟨ι₀ o, hι₀ o⟩ ∈ maximalIdeal (Localization.AtPrime 𝔪a)) ∧

      ∃ ι : AdicCompletion (maximalIdeal (Localization.AtPrime 𝔪a)) (Localization.AtPrime 𝔪a) ≃+* UVCrossingModel O (π ^ m),
        (∀ o : O, ι (algebraMap (Localization.AtPrime 𝔪a) _ (algebraMap (↥R₀) (Localization.AtPrime 𝔪a) ⟨ι₀ o, hι₀ o⟩)) =
          const (π ^ m) o) ∧
        (∃ γ : UVCrossingModel O (π ^ m), IsUnit γ ∧
          ι (algebraMap (Localization.AtPrime 𝔪a) _ (algebraMap (↥R₀) (Localization.AtPrime 𝔪a) ⟨x, hx⟩)) = U (π ^ m) * γ) ∧
        ι (algebraMap (Localization.AtPrime 𝔪a) _ (algebraMap (↥R₀) (Localization.AtPrime 𝔪a) ⟨y, hy⟩)) = V (π ^ m) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_exists_isMaximal_ringEquiv_adicCompletion_atPrime_uvCrossingModel_pow_of_mem_maximalIdeal.solution
