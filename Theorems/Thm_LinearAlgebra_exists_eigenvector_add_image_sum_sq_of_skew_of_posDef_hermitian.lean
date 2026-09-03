import Mathlib
import P2M.Util
import P2M.Sol.S_LinearAlgebra_exists_eigenvector_add_image_sum_sq_of_skew_of_posDef_hermitian

set_option autoImplicit false
theorem LinearAlgebra.exists_eigenvector_add_image_sum_sq_of_skew_of_posDef_hermitian
    (V : Type*) [AddCommGroup V] [Module ℂ V] (M₀ : Submodule ℂ V) [Module.Finite ℂ M₀]
    (B : V → V → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M₀, ∀ w₂ ∈ M₀, ∀ w' ∈ M₀, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ M₀, ∀ w' ∈ M₀, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ M₀, w ≠ 0 → 0 < (B w w).re)
    (ι : Type*) [Fintype ι] (θ : ι → (V →ₗ[ℂ] V))
    (hθM : ∀ i : ι, ∀ w ∈ M₀, θ i w ∈ M₀)
    (hskew : ∀ i : ι, ∀ w ∈ M₀, ∀ w' ∈ M₀, B (θ i w) w' = -B w (θ i w'))
    (c : ℂ) (z : V) (hz : z ∈ M₀) :
    ∃ k ∈ M₀, ∃ x ∈ M₀, (∑ i : ι, θ i * θ i) k = c • k ∧ z = k + ((∑ i : ι, θ i * θ i) x - c • x) := by p2m_exact_reverting @_root_.P2MW.S_LinearAlgebra_exists_eigenvector_add_image_sum_sq_of_skew_of_posDef_hermitian.solution
