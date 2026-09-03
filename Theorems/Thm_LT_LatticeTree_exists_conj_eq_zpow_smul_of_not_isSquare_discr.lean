import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import P2M.Util
import P2M.Sol.S_LT_LatticeTree_exists_conj_eq_zpow_smul_of_not_isSquare_discr

set_option autoImplicit false

open scoped Matrix
open NumberField IsDedekindDomain

theorem LT.LatticeTree.exists_conj_eq_zpow_smul_of_not_isSquare_discr
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K))
    (hγ : ¬ IsSquare (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
      4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) :
    ∃ (x : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K)) (k : ℤ),
      (∃ (γ' : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers K)) (d : ℕ)
          (mu : (v.adicCompletionIntegers K)ˣ) (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)),
        (∀ i j,
          (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j =
            (mu : v.adicCompletionIntegers K) * (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j +
              ϖ ^ d * Y i j) ∧
        (∀ (a : v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})
            (w : Fin 2 → v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}),
          (Y.map (Ideal.Quotient.mk (Ideal.span {ϖ}) :
              v.adicCompletionIntegers K →+* v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})) *ᵥ w = a • w → w = 0) ∧
        ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ k •
            (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)).map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
                : v.adicCompletionIntegers K → v.adicCompletion K)) ∨
      (∃ (γ' : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers K)) (d : ℕ)
          (mu : (v.adicCompletionIntegers K)ˣ) (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K))
          (w : (v.adicCompletionIntegers K)ˣ),
        (∀ i j,
          (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j =
            (mu : v.adicCompletionIntegers K) * (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j +
              ϖ ^ d * Y i j) ∧
        Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : v.adicCompletionIntegers K) ∧ ϖ ∣ Y 0 0 + Y 1 1 ∧
        ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ k •
            (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)).map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
                : v.adicCompletionIntegers K → v.adicCompletion K)) ∨
      (∃ (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) (w : (v.adicCompletionIntegers K)ˣ),
        Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : v.adicCompletionIntegers K) ∧ ϖ ∣ Y 0 0 + Y 1 1 ∧
        ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ k •
            Y.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
              : v.adicCompletionIntegers K → v.adicCompletion K)) := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_exists_conj_eq_zpow_smul_of_not_isSquare_discr.solution
