import Definitions.Def_NumberField_IdeleProductMeasure
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import P2M.Util
import P2M.Sol.S_NumberField_Idele_exists_lintegral_ite_ball_comp_partAt_sPartMeasure_eq_mul_lintegral_sPartMeasure_empty

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal Classical

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem NumberField.Idele.exists_lintegral_ite_ball_comp_partAt_sPartMeasure_eq_mul_lintegral_sPartMeasure_empty
    (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (t₀ : (AdeleRing (𝓞 K) K)ˣ) (_ht₀ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1)
    (nb : ℕ) (_hnb : 0 < nb) :
    ∃ κ : ℝ, 0 < κ ∧
      (∀ f : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable f →
        (∫⁻ t, (if (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then f (NumberField.Idele.partAt K ∅ t) else 0)
            ∂(NumberField.Idele.sPartMeasure K S)) =
          ENNReal.ofReal κ * ∫⁻ t, f t ∂(NumberField.Idele.sPartMeasure K ∅)) ∧
      (∀ f : (AdeleRing (𝓞 K) K)ˣ → ℂ, Integrable f (NumberField.Idele.sPartMeasure K ∅) →
        Integrable (fun t : (AdeleRing (𝓞 K) K)ˣ => if (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then f (NumberField.Idele.partAt K ∅ t) else 0)
            (NumberField.Idele.sPartMeasure K S) ∧
        (∫ t, (if (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then f (NumberField.Idele.partAt K ∅ t) else 0)
            ∂(NumberField.Idele.sPartMeasure K S)) =
          (κ : ℂ) * ∫ t, f t ∂(NumberField.Idele.sPartMeasure K ∅)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Idele_exists_lintegral_ite_ball_comp_partAt_sPartMeasure_eq_mul_lintegral_sPartMeasure_empty.solution
