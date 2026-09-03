import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Theorems.Thm_CerednikDrinfeld_Omega_theta_pmoebius_mul_basePoint
import Theorems.Thm_CerednikDrinfeld_Omega_theta_self_eq_one
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_Omega_theta_pmoebius_basePoint_mul_inv

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (β : G)
    (h : ThetaMultipliable ρ a b z₀ (pmoebius K₀ (ρ β) z₀))
    (h' : ThetaMultipliable ρ a b z₀ (pmoebius K₀ (ρ β⁻¹) z₀)) :
    theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀) * theta ρ a b z₀ (pmoebius K₀ (ρ β⁻¹) z₀) = 1 := by
  rw [← CerednikDrinfeld.Omega.theta_pmoebius_mul_basePoint ρ ha hb hz₀ hz₀a hz₀b β β⁻¹ h h', mul_inv_cancel,
    map_one, pmoebius_one, CerednikDrinfeld.Omega.theta_self_eq_one ρ hz₀a hz₀b]
