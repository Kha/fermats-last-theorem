import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_bddAbove_setOf_coordSub_pow_dvd

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld CerednikDrinfeld.Omega~eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero"

theorem CerednikDrinfeld.Omega.bddAbove_setOf_coordSub_pow_dvd
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)

    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (F : ↥(Omega.holRing ϖ)) (hF : F ≠ 0) (z : ↥(Omega.upperHalfPlane K₀ K)) :
    BddAbove {n : ℕ | Omega.coordSub ϖ z ^ n ∣ F} := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_bddAbove_setOf_coordSub_pow_dvd.solution
