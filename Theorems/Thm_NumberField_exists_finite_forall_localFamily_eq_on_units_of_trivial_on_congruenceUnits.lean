import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem NumberField.exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits
    (K : Type) [Field K] [NumberField K]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) :
    ∃ (n : ℕ) (ρs : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ),
    ∀ (χ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
      (_hχ : ∀ v ∈ SK, ∀ t : (v.adicCompletion K)ˣ, (t : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        Valued.v ((t : v.adicCompletion K) - 1) ≤ idealBound (𝓞 K) N v → χ v t = 1),
    ∃ r : Fin n, ∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        χ v u = ρs r v u := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits.solution
