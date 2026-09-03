import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_exists_subgroup_units_valuationOfNeZero_eq_one_inf_torsion_eq_bot_existsUnique_coset_of_isOpen

set_option autoImplicit false

p2m_open "NumberField~exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul IsDedekindDomain"

open scoped Classical in

theorem NumberField.exists_subgroup_units_valuationOfNeZero_eq_one_inf_torsion_eq_bot_existsUnique_coset_of_isOpen
    (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ F : Subgroup Kˣ,
      (∀ φ ∈ F, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero φ = 1) ∧
      (∀ φ ∈ F, (∃ ζ : (𝓞 K)ˣ, ζ ∈ NumberField.Units.torsion K ∧ ((ζ : 𝓞 K) : K) = (φ : K)) → φ = 1) ∧
      (∀ u : Kˣ, (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero u = 1) →
        ∃ ζ : (𝓞 K)ˣ, ζ ∈ NumberField.Units.torsion K ∧ ∃ φ ∈ F, (u : K) = ((ζ : 𝓞 K) : K) * (φ : K)) ∧
      ∀ (f : HeightOneSpectrum (𝓞 K) → ℤ) (S : Finset (HeightOneSpectrum (𝓞 K))), (∀ v ∈ S, v ∉ T) →
        ∀ U : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ,
          (∀ v ∈ S, IsOpen (U v : Set (v.adicCompletion K)ˣ)) →
          ∃ (n : ℕ) (c : Fin n → Kˣ),
            (∀ j, c j ∈ F ∧ ∀ v ∈ T, f v ∣ Multiplicative.toAdd (v.valuationOfNeZero (c j))) ∧
            ∀ φ ∈ F, (∀ v ∈ T, f v ∣ Multiplicative.toAdd (v.valuationOfNeZero φ)) →
              ∃! j : Fin n,
                (∀ v ∈ S, Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) (φ * (c j)⁻¹) ∈ U v) ∧
                ∀ w : {w : InfinitePlace K // w.IsReal}, 0 < (mixedEmbedding K ((φ * (c j)⁻¹ : Kˣ) : K)).1 w := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_subgroup_units_valuationOfNeZero_eq_one_inf_torsion_eq_bot_existsUnique_coset_of_isOpen.solution
