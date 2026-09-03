import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_v_apply_mul_inv_eq_mul_zpow_neg_sum_of_star

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Omega.v_apply_mul_inv_eq_mul_zpow_neg_sum_of_star
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (T : Finset K₀) (hT : ∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1)
    (hTcov : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1)
    (hTsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 1 ≤ Valued.v (algebraMap K₀ K t - algebraMap K₀ K t'))
    (F : K → K) (c₀ c₀' : Γ₀) (m m' : K₀ → ℤ)
    (hstar : ∀ z : K, (∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v (z - algebraMap K₀ K t)) →
      Valued.v z < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ →
        Valued.v (F z) = c₀ * ∏ t ∈ T, Valued.v (z - algebraMap K₀ K t) ^ (m t))
    (hstar' : ∀ w : K, (∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v (w - algebraMap K₀ K t)) →
      Valued.v w < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ →
        Valued.v (F (w * (algebraMap K₀ K ϖ.ϖ)⁻¹)) = c₀' * ∏ t ∈ T, Valued.v (w - algebraMap K₀ K t) ^ (m' t))
    (w w' : K) (hw : w ∈ affinoid ϖ 0) (hw' : w' ∈ affinoid ϖ 0) :
    Valued.v (F (w * (algebraMap K₀ K ϖ.ϖ)⁻¹)) =
      Valued.v (F w') * Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (-(∑ t ∈ T, m t)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_v_apply_mul_inv_eq_mul_zpow_neg_sum_of_star.solution
