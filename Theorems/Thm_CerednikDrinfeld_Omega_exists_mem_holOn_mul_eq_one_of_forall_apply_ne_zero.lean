import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_mem_holOn_mul_eq_one_of_forall_apply_ne_zero

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega~exists_forall_v_apply_eq_on_circle_of_mem_holOn"

theorem CerednikDrinfeld.Omega.exists_mem_holOn_mul_eq_one_of_forall_apply_ne_zero
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (n : ℕ)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {u : ↥(affinoid ϖ n) → K} (hu : u ∈ holOn K (affinoid ϖ n)) (h0 : ∀ z : ↥(affinoid ϖ n), u z ≠ 0) :
    ∃ w : ↥(affinoid ϖ n) → K, w ∈ holOn K (affinoid ϖ n) ∧ u * w = 1 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_mem_holOn_mul_eq_one_of_forall_apply_ne_zero.solution
