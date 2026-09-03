import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_sub_mul_log_le_tsum_ncard_isArithFrobAt
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open NumberField

theorem NumberField.sub_mul_log_le_tsum_ncard_isArithFrobAt
    (L : Type) [Field L] [NumberField L] (σ : L ≃ₐ[ℚ] L) (δ : ℝ) (hδ : 0 < δ) :
    ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      (1 / (orderOf σ : ℝ) - δ) * Real.log (1 / (s - 1)) ≤
        ∑' p : Nat.Primes, (({P : Ideal (𝓞 L) | P.IsMaximal ∧ ((p : ℕ) : 𝓞 L) ∈ P ∧
            IsArithFrobAt ℤ σ P}.ncard : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-s) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_sub_mul_log_le_tsum_ncard_isArithFrobAt.solution
