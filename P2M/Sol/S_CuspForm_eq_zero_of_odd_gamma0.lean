import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import P2M.Util
namespace P2MW.S_CuspForm_eq_zero_of_odd_gamma0

set_option autoImplicit false

theorem solution (N : ℕ) (k : ℤ) (hk : Odd k)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : f = 0 := by
  have hΓ : (-1 : GL (Fin 2) ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := by
    refine ⟨-1, ?_, ?_⟩
    · simp [CongruenceSubgroup.Gamma0_mem]
    · ext i j
      simp [Matrix.SpecialLinearGroup.coe_int_neg]
  ext z
  have hf := SlashInvariantForm.slash_action_eqn'' f hΓ z
  rw [UpperHalfPlane.neg_smul, one_smul, UpperHalfPlane.denom_neg, UpperHalfPlane.denom_one,
    Odd.neg_one_zpow hk] at hf
  have h2 : (2 : ℂ) * f z = 0 := by linear_combination hf
  rw [CuspForm.zero_apply]
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
