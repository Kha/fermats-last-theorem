import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (n : ℕ)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {G : ↥(affinoid ϖ n) → K} (hG : G ∈ holOn K (affinoid ϖ n)) (hG0 : ∀ z : ↥(affinoid ϖ n), G z ≠ 0) :
    ∃ δ : K, δ ≠ 0 ∧ ∀ z : ↥(affinoid ϖ n), Valued.v δ ≤ Valued.v (G z) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero.solution
