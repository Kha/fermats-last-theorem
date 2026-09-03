import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_theta_isometricAut

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.theta_isometricAut
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (s : IsometricAut K₀ K) {a b z₀ z : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz : z ∈ upperHalfPlane K₀ K) :
    theta ρ (s.toRingEquiv a) (s.toRingEquiv b) (s.toRingEquiv z₀) (s.toRingEquiv z) =
      s.toRingEquiv (theta ρ a b z₀ z) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_theta_isometricAut.solution
