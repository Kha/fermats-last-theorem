import Definitions.Def_AutomorphicForm_WindingDatum
import P2M.Util
import P2M.Sol.S_AutomorphicForm_WindingDatum_exists_clm_noAtomicMass_forall_apply_fourier_eq_coeff

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.WindingDatum.exists_clm_noAtomicMass_forall_apply_fourier_eq_coeff
    (r d c : ℕ) (𝒟 : AutomorphicForm.WindingDatum r d c) :
    (∀ (i : ℕ) (n : Fin d → ℤ), Summable (𝒟.fibreTerm i n)) ∧
    (∀ n : Fin d → ℤ, Summable fun i : ℕ => 𝒟.lam i * 𝒟.fibreCoeff i n) ∧
    (∃ B : ℝ, ∀ n : Fin d → ℤ, ‖𝒟.coeff n‖ ≤ B) ∧
    ∃ μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ,
      (∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin d → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) ∧
      ∀ (n : Fin d → ℤ) (e : C((Fin d → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) → μ e = 𝒟.coeff n := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_WindingDatum_exists_clm_noAtomicMass_forall_apply_fourier_eq_coeff.solution
