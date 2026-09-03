import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_theta_pmoebius_mul_basePoint

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.theta_pmoebius_mul_basePoint
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (β₁ β₂ : G)
    (h₁ : ThetaMultipliable ρ a b z₀ (pmoebius K₀ (ρ β₁) z₀))
    (h₂ : ThetaMultipliable ρ a b z₀ (pmoebius K₀ (ρ β₂) z₀)) :
    theta ρ a b z₀ (pmoebius K₀ (ρ (β₁ * β₂)) z₀) =
      theta ρ a b z₀ (pmoebius K₀ (ρ β₁) z₀) * theta ρ a b z₀ (pmoebius K₀ (ρ β₂) z₀) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_theta_pmoebius_mul_basePoint.solution
