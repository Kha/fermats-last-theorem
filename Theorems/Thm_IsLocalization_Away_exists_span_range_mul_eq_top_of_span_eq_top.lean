import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalization_Away_exists_span_range_mul_eq_top_of_span_eq_top

set_option autoImplicit false
universe u

theorem IsLocalization.Away.exists_span_range_mul_eq_top_of_span_eq_top
    {B : Type u} [CommRing B] {n : ℕ} (f : Fin n → B) (hf : Ideal.span (Set.range f) = ⊤)
    (L : Fin n → Type u) [∀ i, CommRing (L i)] [∀ i, Algebra B (L i)] [∀ i, IsLocalization.Away (f i) (L i)]
    (m : Fin n → ℕ) (g : ∀ i, Fin (m i) → L i) (hg : ∀ i, Ideal.span (Set.range (g i)) = ⊤) :
    ∃ (b : ∀ i, Fin (m i) → B) (e : ∀ i, Fin (m i) → ℕ),
      (∀ i k, algebraMap B (L i) (b i k) = g i k * algebraMap B (L i) (f i) ^ (e i k)) ∧
      Ideal.span (Set.range (fun ik : (Σ i : Fin n, Fin (m i)) => f ik.1 * b ik.1 ik.2)) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_IsLocalization_Away_exists_span_range_mul_eq_top_of_span_eq_top.solution
