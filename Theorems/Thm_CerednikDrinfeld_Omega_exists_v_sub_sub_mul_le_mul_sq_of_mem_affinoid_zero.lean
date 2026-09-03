import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_v_sub_sub_mul_le_mul_sq_of_mem_affinoid_zero

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_v_sub_sub_mul_le_mul_sq_of_mem_affinoid_zero
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (f : ↥(holRing ϖ)) (M : Γ₀)
    (hM : ∀ z : ↥(upperHalfPlane K₀ K), (z : K) ∈ affinoid ϖ 0 → Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) ≤ M)
    (b : ↥(upperHalfPlane K₀ K)) (hb : (b : K) ∈ affinoid ϖ 0) :
    ∃ d : K, Valued.v d ≤ M ∧
      ∀ z : ↥(upperHalfPlane K₀ K), Valued.v ((z : K) - (b : K)) < 1 →
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z - (f : ↥(upperHalfPlane K₀ K) → K) b - d * ((z : K) - (b : K))) ≤
          M * Valued.v ((z : K) - (b : K)) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_v_sub_sub_mul_le_mul_sq_of_mem_affinoid_zero.solution
