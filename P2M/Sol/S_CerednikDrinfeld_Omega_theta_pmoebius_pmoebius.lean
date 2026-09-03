import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_Omega_theta_pmoebius_pmoebius

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K] [TopologicalSpace K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b w z : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hw : w ∈ upperHalfPlane K₀ K) (hz : z ∈ upperHalfPlane K₀ K) (β : G) :
    theta ρ a b (pmoebius K₀ (ρ β) w) (pmoebius K₀ (ρ β) z) = theta ρ a b w z := by
  have hfac : ∀ γ : G,
      thetaFactor ρ a b (pmoebius K₀ (ρ β) w) (pmoebius K₀ (ρ β) z) (β * γ) = thetaFactor ρ a b w z γ := by
    intro γ
    rw [thetaFactor, thetaFactor, map_mul, pmoebius_mul K₀ ha, pmoebius_mul K₀ hb]
    exact CerednikDrinfeld.Omega.crossRatio_pmoebius (ρ β) hz hw (pmoebius_mem_upperHalfPlane K₀ ha _)
      (pmoebius_mem_upperHalfPlane K₀ hb _)
  rw [theta, theta, ← Equiv.tprod_eq (Equiv.mulLeft β)]
  exact tprod_congr fun γ => hfac γ
