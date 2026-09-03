import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_exists_finset_sum_mul_eq_of_isHomogeneous_of_mem_span

set_option autoImplicit false

theorem MvPolynomial.exists_finset_sum_mul_eq_of_isHomogeneous_of_mem_span
    {σ A : Type} [CommRing A] (J₀ : Set (MvPolynomial σ A))
    (hJ₀ : ∀ G ∈ J₀, ∃ e : ℕ, G.IsHomogeneous e)
    {d : ℕ} {F : MvPolynomial σ A} (hF : F.IsHomogeneous d) (hFJ : F ∈ Ideal.span J₀) :
    ∃ (s : Finset (MvPolynomial σ A)) (e : MvPolynomial σ A → ℕ) (c : MvPolynomial σ A → MvPolynomial σ A),
      ↑s ⊆ J₀ ∧
      (∀ G ∈ s, e G ≤ d ∧ G.IsHomogeneous (e G) ∧ (c G).IsHomogeneous (d - e G)) ∧
      F = ∑ G ∈ s, c G * G := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_finset_sum_mul_eq_of_isHomogeneous_of_mem_span.solution
