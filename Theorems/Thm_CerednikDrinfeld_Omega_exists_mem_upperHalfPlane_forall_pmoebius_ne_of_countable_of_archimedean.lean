import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_mem_upperHalfPlane_forall_pmoebius_ne_of_countable_of_archimedean

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_mem_upperHalfPlane_forall_pmoebius_ne_of_countable_of_archimedean
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {G : Type} [Group G] [Countable G] (ρ : G →* PGL(2, K₀))
    {z : K} (hz : z ∈ upperHalfPlane K₀ K) :
    ∃ b z₀ : K, b ∈ upperHalfPlane K₀ K ∧ z₀ ∈ upperHalfPlane K₀ K ∧
      (∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z) ∧ (∀ γ : G, pmoebius K₀ (ρ γ) z ≠ z₀) ∧
      (∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_mem_upperHalfPlane_forall_pmoebius_ne_of_countable_of_archimedean.solution
