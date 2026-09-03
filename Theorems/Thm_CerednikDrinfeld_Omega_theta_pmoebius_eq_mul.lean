import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_theta_pmoebius_eq_mul

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.theta_pmoebius_eq_mul
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ z : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz : z ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (β : G)
    (hΘ : ThetaMultipliable ρ a b z₀ z)
    (hΘ₀ : ThetaMultipliable ρ a b (pmoebius K₀ (ρ β⁻¹) z₀) z₀) :
    theta ρ a b z₀ (pmoebius K₀ (ρ β) z) =
      theta ρ a b (pmoebius K₀ (ρ β⁻¹) z₀) z₀ * theta ρ a b z₀ z := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_theta_pmoebius_eq_mul.solution
