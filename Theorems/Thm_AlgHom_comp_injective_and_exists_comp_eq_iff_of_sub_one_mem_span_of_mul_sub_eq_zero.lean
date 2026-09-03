import Mathlib
import P2M.Util
import P2M.Sol.S_AlgHom_comp_injective_and_exists_comp_eq_iff_of_sub_one_mem_span_of_mul_sub_eq_zero

theorem AlgHom.comp_injective_and_exists_comp_eq_iff_of_sub_one_mem_span_of_mul_sub_eq_zero
    {A K : Type} [CommRing A] [CommRing K] [Algebra ℤ A] [Algebra ℤ K]
    (ι : A →ₐ[ℤ] K) (ε : K →ₐ[ℤ] ℤ) (p : ℕ) (a : K)
    (hι : Function.Injective ι)
    (htf : ∀ k : K, (p : K) * k = 0 → k = 0)
    (h1 : a - 1 ∈ Ideal.span {(p : K)})
    (h2 : ∀ k : K, a * (k - algebraMap ℤ K (ε k)) = 0)
    (h3 : ∀ k : K, ∃ (n : ℕ) (h : A), (p : K) ^ n * k = ι h)
    (R : Type) [CommRing R] :
    (∀ f g : K →ₐ[ℤ] R, f.comp ι = g.comp ι → f = g) ∧
      ∀ g : A →ₐ[ℤ] R, (∃ f : K →ₐ[ℤ] R, f.comp ι = g) ↔
        ∃ b : R, b - 1 ∈ Ideal.span {(p : R)} ∧
          ∀ h : A, b * (g h - algebraMap ℤ R (ε (ι h))) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_comp_injective_and_exists_comp_eq_iff_of_sub_one_mem_span_of_mul_sub_eq_zero.solution
