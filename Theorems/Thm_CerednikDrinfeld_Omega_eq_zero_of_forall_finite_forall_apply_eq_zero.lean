import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_eq_zero_of_forall_finite_forall_apply_eq_zero

set_option autoImplicit false

open CerednikDrinfeld.Omega hiding affinoid_nonempty_of_exists_finset_cover finite_setOf_apply_eq_zero_of_mem_holOn_affinoid

theorem CerednikDrinfeld.Omega.eq_zero_of_forall_finite_forall_apply_eq_zero
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (Ψ : ↥(holRing ϖ))
    (h : ∀ n : ℕ, ∃ Z : Set ↥(affinoid ϖ n), Z.Finite ∧ ∀ z : ↥(affinoid ϖ n), z ∉ Z →
      (Ψ : ↥(upperHalfPlane K₀ K) → K) ⟨(z : K), affinoid_subset_upperHalfPlane ϖ n z.2⟩ = 0) :
    Ψ = 0 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_eq_zero_of_forall_finite_forall_apply_eq_zero.solution
