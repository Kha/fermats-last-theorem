import Mathlib
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_GaloisRep_sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem GaloisRep.sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective
    {Q : Type} [Group Q] [Finite Q] (π : Γℚ →* Q) (hπ : Function.Surjective π)
    (hπc : GaloisFactorsThroughFiniteLevel π)
    (C : Set Q) (hC : ∀ g h : Q, g ∈ C → h * g * h⁻¹ ∈ C)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      ((Nat.card C : ℝ) / Nat.card Q - δ) * Real.log (1 / (s - 1)) ≤
        ∑' p : {p : ℕ // p.Prime ∧
            (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
              ∀ σ ∈ A.inertiaSubgroupIn ℚ, π σ = 1) ∧
            ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p ∧
              ∃ σ : Γℚ, A.IsFrobeniusAt σ p ∧ π σ ∈ C},
          ((p : ℕ) : ℝ) ^ (-s) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective.solution
