import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_holRing_div_eq_theta

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld.Omega~finite_setOf_pmoebius_mem_affinoid~eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt"

theorem CerednikDrinfeld.Omega.exists_holRing_div_eq_theta
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) :
    ∃ F H : ↥(holRing ϖ),
      H ∈ nonZeroDivisors ↥(holRing ϖ) ∧
      (∀ z : ↥(upperHalfPlane K₀ K),
        (H : ↥(upperHalfPlane K₀ K) → K) z = 0 ↔ ∃ γ : G, pmoebius K₀ (ρ γ) b = (z : K)) ∧
      (∀ z : ↥(upperHalfPlane K₀ K),
        (F : ↥(upperHalfPlane K₀ K) → K) z = 0 ↔ ∃ γ : G, pmoebius K₀ (ρ γ) a = (z : K)) ∧
      (∀ z : ↥(upperHalfPlane K₀ K), (¬ ∃ γ : G, pmoebius K₀ (ρ γ) b = (z : K)) →
        (F : ↥(upperHalfPlane K₀ K) → K) z / (H : ↥(upperHalfPlane K₀ K) → K) z = theta ρ a b z₀ (z : K)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_holRing_div_eq_theta.solution
