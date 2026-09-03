import Mathlib
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import P2M.Util
import P2M.Sol.S_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_unipotentMoment_eq_mul_laurentCoeff_zero

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem AutomorphicForm.SatakeCombination.sum_slotCoeff_mul_unipotentMoment_eq_mul_laurentCoeff_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (v : HeightOneSpectrum (𝓞 K)) (w' : HeightOneSpectrum (𝓞 L))
    (ξ ζ σr s : ℂ)
    (hσ : σr ^ 2 = HeckeEigensystem.cNorm v * ξ)
    (hs : ((Real.sqrt (Ideal.absNorm w'.asIdeal : ℝ) : ℂ) * s) = σr ^ SatakeCombination.slotDeg K L ws v)
    (hζ : ξ ^ SatakeCombination.slotDeg K L ws v = ζ)
    (hNws : Ideal.absNorm (ws v).1.asIdeal = Ideal.absNorm v.asIdeal ^ SatakeCombination.slotDeg K L ws v)
    (k j : ℕ) :
    ∑ r ∈ (SatakeCombination.slotWord K L ws v k j).support,
      SatakeCombination.slotCoeff K L ws v k j r *
        ((1 + (-1 : ℂ) ^ r 0) / 2 * (4 * (HeckeEigensystem.cNorm v * ξ)) ^ (r 0 / 2) *
          ((∏ n ∈ Finset.range (r 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) * ξ ^ r 1) =
      ((Real.sqrt (Ideal.absNorm w'.asIdeal : ℝ) : ℂ) * s) ^ k * ζ ^ j *
        ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial ℂ).coeff 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_unipotentMoment_eq_mul_laurentCoeff_zero.solution
