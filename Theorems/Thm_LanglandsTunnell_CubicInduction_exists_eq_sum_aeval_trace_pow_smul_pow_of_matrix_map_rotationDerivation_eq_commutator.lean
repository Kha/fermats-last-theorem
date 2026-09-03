import Definitions.Def_LanglandsTunnell_CubicInduction_KFinite3
import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_eq_sum_aeval_trace_pow_smul_pow_of_matrix_map_rotationDerivation_eq_commutator

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.exists_eq_sum_aeval_trace_pow_smul_pow_of_matrix_map_rotationDerivation_eq_commutator
    (M : Matrix (Fin 3) (Fin 3) (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ)) :
    let Y : Matrix (Fin 3) (Fin 3) (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      Matrix.of fun a b => if h : a ≤ b then MvPolynomial.X ⟨(a, b), h⟩ else MvPolynomial.X ⟨(b, a), le_of_not_ge h⟩
    let K : Fin 3 → Fin 3 → Matrix (Fin 3) (Fin 3) (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      fun i j => Matrix.single i j 1 - Matrix.single j i 1
    let D : Fin 3 → Fin 3 →
        Derivation ℂ (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ)
          (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      fun i j => MvPolynomial.mkDerivation ℂ fun v => (K i j * Y - Y * K i j) v.1.1 v.1.2
    (∀ i j : Fin 3, M.map (D i j) = K i j * M - M * K i j) →
      ∃ G : Fin 3 → MvPolynomial (Fin 3) ℂ,
        M = ∑ n : Fin 3,
          MvPolynomial.aeval (fun m : Fin 3 => (Y ^ ((m : ℕ) + 1)).trace) (G n) • Y ^ (n : ℕ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_sum_aeval_trace_pow_smul_pow_of_matrix_map_rotationDerivation_eq_commutator.solution
