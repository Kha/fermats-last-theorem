import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt

set_option autoImplicit false

open scoped MatrixGroups
open Filter CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (n : ℕ) {a b z₀ : K} (ha : a ∈ affinoid ϖ n) (hb : b ∈ affinoid ϖ n) (hz₀ : z₀ ∈ affinoid ϖ n)
    (ε : Γ₀) (hε : ε ≠ 0) :
    ∀ᶠ γ in cofinite, ∀ z ∈ affinoid ϖ n, Valued.v (thetaFactor ρ a b z₀ z γ - 1) < ε := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt.solution
