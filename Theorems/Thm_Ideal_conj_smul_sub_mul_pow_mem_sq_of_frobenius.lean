import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_conj_smul_sub_mul_pow_mem_sq_of_frobenius

universe u v
theorem Ideal.conj_smul_sub_mul_pow_mem_sq_of_frobenius {B : Type u} [CommRing B] {G : Type v} [Group G]
    [MulSemiringAction G B] (𝔓 : Ideal B) {ϖ : B} (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) {t : B}
    (ht : σ • ϖ - ϖ * t ∈ 𝔓 ^ 2) {q : ℕ} {φ : G} (hφ : ∀ x : B, φ • x - x ^ q ∈ 𝔓)
    (hφP : ∀ x ∈ 𝔓, φ • x ∈ 𝔓) (hφP' : ∀ x ∈ 𝔓, φ⁻¹ • x ∈ 𝔓) :
    (φ * σ * φ⁻¹) • ϖ - ϖ * t ^ q ∈ 𝔓 ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_conj_smul_sub_mul_pow_mem_sq_of_frobenius.solution
