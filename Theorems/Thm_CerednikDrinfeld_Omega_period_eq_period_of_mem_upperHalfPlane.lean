import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_period_eq_period_of_mem_upperHalfPlane

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld.Omega~theta_pmoebius_basePoint_mul_inv"

theorem CerednikDrinfeld.Omega.period_eq_period_of_mem_upperHalfPlane
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a a' z₀ : K}
    (ha : a ∈ upperHalfPlane K₀ K) (ha' : a' ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀a' : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ z₀)
    (hΘ : ∀ x ∈ upperHalfPlane K₀ K, ∀ y ∈ upperHalfPlane K₀ K, ∀ z ∈ upperHalfPlane K₀ K,
      ThetaMultipliable ρ x y z₀ z)
    (α β : G) :
    period ρ a z₀ α β = period ρ a' z₀ α β := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_period_eq_period_of_mem_upperHalfPlane.solution
