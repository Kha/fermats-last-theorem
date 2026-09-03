import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.finite_setOf_pmoebius_mem_affinoid
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (n : ℕ) {b : K} (hb : b ∈ affinoid ϖ n) :
    {γ : G | pmoebius K₀ (ρ γ) b ∈ affinoid ϖ n}.Finite := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid.solution
