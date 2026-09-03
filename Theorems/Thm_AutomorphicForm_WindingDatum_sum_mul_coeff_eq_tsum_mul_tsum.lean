import Mathlib
import Definitions.Def_AutomorphicForm_WindingDatum
import P2M.Util
import P2M.Sol.S_AutomorphicForm_WindingDatum_sum_mul_coeff_eq_tsum_mul_tsum

theorem AutomorphicForm.WindingDatum.sum_mul_coeff_eq_tsum_mul_tsum
    {r d c : ℕ} (𝒟 : AutomorphicForm.WindingDatum r d c) (B : Finset (Fin d → ℤ)) (G : (Fin d → ℤ) → ℂ)
    (hG : ∀ n ∉ B, G n = 0) :
    (∀ i : ℕ, Summable fun γ : 𝒟.sub i =>
        ‖G ((γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + 𝒟.n₀ i) *
          (𝒟.Ψ i (𝒟.x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) *
            ∏ j, fourier (𝒟.m i j) (𝒟.θ₀ i j + 𝒟.χ ⟨(γ : (Fin r → ℝ) × (Fin d → ℤ)), 𝒟.hsub i γ.2⟩ j))‖) ∧
    (Summable fun i : ℕ => ‖𝒟.lam i * ∑' γ : 𝒟.sub i,
        G ((γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + 𝒟.n₀ i) *
          (𝒟.Ψ i (𝒟.x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) *
            ∏ j, fourier (𝒟.m i j) (𝒟.θ₀ i j + 𝒟.χ ⟨(γ : (Fin r → ℝ) × (Fin d → ℤ)), 𝒟.hsub i γ.2⟩ j))‖) ∧
    ∑ n ∈ B, G n * 𝒟.coeff n = ∑' i : ℕ, 𝒟.lam i * ∑' γ : 𝒟.sub i,
        G ((γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + 𝒟.n₀ i) *
          (𝒟.Ψ i (𝒟.x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) *
            ∏ j, fourier (𝒟.m i j) (𝒟.θ₀ i j + 𝒟.χ ⟨(γ : (Fin r → ℝ) × (Fin d → ℤ)), 𝒟.hsub i γ.2⟩ j)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_WindingDatum_sum_mul_coeff_eq_tsum_mul_tsum.solution
