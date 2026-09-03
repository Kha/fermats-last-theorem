import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers
attribute [-simp] LocalGL2.swapUnit_val

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem Matrix.exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers
    (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (Y Yi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ)
    (hpYi : ∀ i j, ((p : v.adicCompletion ℚ) • Yi) i j ∈ v.adicCompletionIntegers ℚ)
    (hYi : ¬ ∀ i j, Yi i j ∈ v.adicCompletionIntegers ℚ)
    (hpY : ¬ ∀ i j, ((p : v.adicCompletion ℚ)⁻¹ • Y) i j ∈ v.adicCompletionIntegers ℚ) :
    ∃ K₁ K₁i K₂ K₂i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, K₁ i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, K₁i i j ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ i j, K₂ i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, K₂i i j ∈ v.adicCompletionIntegers ℚ) ∧
      K₁ * K₁i = 1 ∧ K₁i * K₁ = 1 ∧ K₂ * K₂i = 1 ∧ K₂i * K₂ = 1 ∧
      Y = K₁ * !![1, 0; 0, (p : v.adicCompletion ℚ)] * K₂ := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers.solution
