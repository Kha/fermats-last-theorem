import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_coeff_mem_of_sum_aeval_mul_mem_of_unique_pi_residue_repr

open AlgebraicCurve IsLocalRing Polynomial

theorem AlgebraicCurve.RegularProlongation.coeff_mem_of_sum_aeval_mul_mem_of_unique_pi_residue_repr
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] [Nonempty ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (d : ℕ) (z : Fin d → F) (hzO : ∀ τ i, z τ ∈ (R i).integers)
    (huniqres : ∀ q q' : Fin d → Polynomial (IsLocalRing.ResidueField A),
      (∀ i, ∑ τ, Polynomial.aeval ((R i).residue ⟨f, hf i⟩) (q τ)
          * (R i).residue ⟨z τ, hzO τ i⟩
        = ∑ τ, Polynomial.aeval ((R i).residue ⟨f, hf i⟩) (q' τ)
          * (R i).residue ⟨z τ, hzO τ i⟩) →
      q = q')
    (r : Fin d → Polynomial L)
    (hsum : ∀ i, ∑ τ, Polynomial.aeval f (r τ) * z τ ∈ (R i).integers) :
    ∀ τ j, (r τ).coeff j ∈ A := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_coeff_mem_of_sum_aeval_mul_mem_of_unique_pi_residue_repr.solution
