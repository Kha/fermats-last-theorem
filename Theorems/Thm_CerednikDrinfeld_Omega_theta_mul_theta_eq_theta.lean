import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_theta_mul_theta_eq_theta

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.theta_mul_theta_eq_theta
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b c z₀ z : K}
    (hzb : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (hab : ThetaMultipliable ρ a b z₀ z) (hbc : ThetaMultipliable ρ b c z₀ z) :
    theta ρ a b z₀ z * theta ρ b c z₀ z = theta ρ a c z₀ z := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_theta_mul_theta_eq_theta.solution
