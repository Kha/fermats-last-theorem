import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul
    (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (Λ : AddSubgroup ((Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)))
      (Log : Kˣ → (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)),
      (∀ u : Kˣ, Log u =
        (fun i => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) *
            Real.log (((Fintype.equivFin (InfinitePlace K)).symm i) (u : K)),
          fun j => Multiplicative.toAdd ((T.equivFin.symm j).1.valuationOfNeZero u))) ∧
      (∀ u u' : Kˣ, Log (u * u') = Log u + Log u') ∧
      (∀ γ, γ ∈ Λ ↔ ∃ u : Kˣ,
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero u = 1) ∧ Log u = γ) ∧
      DiscreteTopology Λ ∧
      (∀ γ ∈ Λ, ∑ i, γ.1 i =
        ∑ j, -Real.log (Ideal.absNorm (T.equivFin.symm j).1.asIdeal : ℝ) * (γ.2 j : ℝ)) ∧
      (∀ u : Kˣ, (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero u = 1) →
        (Log u = 0 ↔ ∃ ζ : (𝓞 K)ˣ, ζ ∈ NumberField.Units.torsion K ∧ ((ζ : 𝓞 K) : K) = (u : K))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_addSubgroup_discreteTopology_units_log_valuation_sum_eq_neg_sum_log_absNorm_mul.solution
