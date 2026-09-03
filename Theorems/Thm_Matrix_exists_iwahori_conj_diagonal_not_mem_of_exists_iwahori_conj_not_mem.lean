import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_iwahori_conj_diagonal_not_mem_of_exists_iwahori_conj_not_mem

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem Matrix.exists_iwahori_conj_diagonal_not_mem_of_exists_iwahori_conj_not_mem
    (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (Y Yi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ) (hY10 : (p : v.adicCompletion ℚ)⁻¹ * Y 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hpYi : ∀ i j, ((p : v.adicCompletion ℚ) • Yi) i j ∈ v.adicCompletionIntegers ℚ)
    (hpYi10 : (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ) • Yi) 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hYi : ¬ ((∀ i j, Yi i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * Yi 1 0 ∈ v.adicCompletionIntegers ℚ))
    (hpY : ¬ ((∀ i j, ((p : v.adicCompletion ℚ)⁻¹ • Y) i j ∈ v.adicCompletionIntegers ℚ) ∧
      (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ)⁻¹ • Y) 1 0 ∈ v.adicCompletionIntegers ℚ))
    (hZ : ∃ Z : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), (∀ i j, Z i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * Z 1 0 ∈ v.adicCompletionIntegers ℚ ∧
      ¬ ∀ i j, (Y * Z * Yi) i j ∈ v.adicCompletionIntegers ℚ) :
    ∃ X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), (∀ i j, X i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * X 1 0 ∈ v.adicCompletionIntegers ℚ ∧
      ¬ ∀ i j, (Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((p : v.adicCompletion ℚ))⁻¹] * (Yi * X * Y) *
        Matrix.diagonal ![(1 : v.adicCompletion ℚ), (p : v.adicCompletion ℚ)]) i j ∈ v.adicCompletionIntegers ℚ := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_iwahori_conj_diagonal_not_mem_of_exists_iwahori_conj_not_mem.solution
