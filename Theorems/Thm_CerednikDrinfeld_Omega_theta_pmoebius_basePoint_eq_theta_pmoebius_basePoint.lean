import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld.Omega~theta_pmoebius_pmoebius"

theorem CerednikDrinfeld.Omega.theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ z₁ : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz₁ : z₁ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (hz₁a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₁) (hz₁b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₁)
    (hΘ : ∀ w ∈ upperHalfPlane K₀ K, ∀ z ∈ upperHalfPlane K₀ K, ThetaMultipliable ρ a b w z) (β : G) :
    theta ρ a b z₁ (pmoebius K₀ (ρ β) z₁) = theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint.solution
