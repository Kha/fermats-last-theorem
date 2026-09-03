import Mathlib
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import P2M.Util
import P2M.Sol.S_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_unipotentEdgeMoment_eq_mul_sum_laurentCoeff_edge

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem AutomorphicForm.SatakeCombination.sum_slotCoeff_mul_unipotentEdgeMoment_eq_mul_sum_laurentCoeff_edge
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
        ((1 + (-1 : ℂ) ^ r 0) * (4 * (HeckeEigensystem.cNorm v * ξ)) ^ (r 0 / 2) * ξ ^ r 1) =
      ((Real.sqrt (Ideal.absNorm w'.asIdeal : ℝ) : ℂ) * s) ^ k * ζ ^ j *
        ∑ n ∈ Finset.Icc (-(k : ℤ)) k,
          ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial ℂ).coeff n *
            (1 + (-1 : ℂ) ^ (SatakeCombination.slotDeg K L ws v * n.natAbs)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_unipotentEdgeMoment_eq_mul_sum_laurentCoeff_edge.solution
