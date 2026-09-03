import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_sum_iteratedFDeriv_two_comp_conj_eq_of_mul_conjTranspose_eq_one

set_option autoImplicit false

open NumberField
open scoped Classical in

theorem NumberField.mixedEmbedding.sum_iteratedFDeriv_two_comp_conj_eq_of_mul_conjTranspose_eq_one
    (K : Type) [Field K] [NumberField K]
    (U : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) (hU : U * U.conjTranspose = 1)
    (F : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ) (hF : ContDiff ℝ 2 F)
    (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) :
    ∑ p : Fin 2 × Fin 2 × mixedEmbedding.index K,
        iteratedFDeriv ℝ 2
          (fun X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K =>
            F (Matrix.of.symm (U * Matrix.of X * U.conjTranspose))) E
          (fun _ => Matrix.of.symm
            (Matrix.of E * Matrix.single p.1 p.2.1 (mixedEmbedding.stdBasis K p.2.2))) =
      ∑ p : Fin 2 × Fin 2 × mixedEmbedding.index K,
        iteratedFDeriv ℝ 2 F (Matrix.of.symm (U * Matrix.of E * U.conjTranspose))
          (fun _ => Matrix.of.symm
            (Matrix.of (Matrix.of.symm (U * Matrix.of E * U.conjTranspose)) *
              Matrix.single p.1 p.2.1 (mixedEmbedding.stdBasis K p.2.2))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_sum_iteratedFDeriv_two_comp_conj_eq_of_mul_conjTranspose_eq_one.solution
