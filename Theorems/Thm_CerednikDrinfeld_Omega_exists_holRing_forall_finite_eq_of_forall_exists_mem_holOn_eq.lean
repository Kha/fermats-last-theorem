import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_holRing_forall_finite_eq_of_forall_exists_mem_holOn_eq

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega~finite_setOf_apply_eq_zero_disc_of_mem_holOn"

theorem CerednikDrinfeld.Omega.exists_holRing_forall_finite_eq_of_forall_exists_mem_holOn_eq
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (Ψ : ↥(upperHalfPlane K₀ K) → K)
    (h : ∀ n : ℕ, ∃ ψ : ↥(affinoid ϖ n) → K, ψ ∈ holOn K (affinoid ϖ n) ∧
      ∃ Z : Set ↥(affinoid ϖ n), Z.Finite ∧
        ∀ z : ↥(affinoid ϖ n), z ∉ Z → Ψ ⟨(z : K), affinoid_subset_upperHalfPlane ϖ n z.2⟩ = ψ z) :
    ∃ Φ : ↥(holRing ϖ), ∀ n : ℕ, ∃ Z : Set ↥(affinoid ϖ n), Z.Finite ∧
      ∀ z : ↥(affinoid ϖ n), z ∉ Z →
        Ψ ⟨(z : K), affinoid_subset_upperHalfPlane ϖ n z.2⟩ =
          (Φ : ↥(upperHalfPlane K₀ K) → K) ⟨(z : K), affinoid_subset_upperHalfPlane ϖ n z.2⟩ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_holRing_forall_finite_eq_of_forall_exists_mem_holOn_eq.solution
