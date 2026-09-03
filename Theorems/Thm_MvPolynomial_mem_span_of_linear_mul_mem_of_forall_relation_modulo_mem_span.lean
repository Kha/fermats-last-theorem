import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_mem_span_of_linear_mul_mem_of_forall_relation_modulo_mem_span

set_option autoImplicit false

open MvPolynomial

theorem MvPolynomial.mem_span_of_linear_mul_mem_of_forall_relation_modulo_mem_span
    (n m g : ℕ) (K : Type) [Field K] (F : Fin g → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous m) (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    (hcol : ∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous m →
      ℓ * f ∈ Ideal.span (Set.range F) → f ∈ Ideal.span (Set.range F))
    (hrel : ∀ (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K), (∀ i, (c i).IsHomogeneous d) →
      ∑ i, c i * F i ∈ Ideal.span {ℓ} →
      c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
        {l : Fin g → MvPolynomial (Fin (n + 1)) K |
          (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i ∈ Ideal.span {ℓ}})
    (k : ℕ) (hk : m ≤ k) (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous k)
    (h : ℓ * f ∈ Ideal.span (Set.range F)) : f ∈ Ideal.span (Set.range F) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_mem_span_of_linear_mul_mem_of_forall_relation_modulo_mem_span.solution
