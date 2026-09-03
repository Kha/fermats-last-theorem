import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_theta_pmoebius_eq_theta_of_mulEquiv_of_apply_eq_conj

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.theta_pmoebius_eq_theta_of_mulEquiv_of_apply_eq_conj
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K] [TopologicalSpace K]
    {G₁ G₂ : Type*} [Group G₁] [Group G₂] (ρ₁ : G₁ →* PGL(2, K₀)) (ρ₂ : G₂ →* PGL(2, K₀))
    (e : G₁ ≃* G₂) (n : PGL(2, K₀)) (he : ∀ g : G₁, ρ₂ (e g) = n * ρ₁ g * n⁻¹)
    {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (w : K) (hw : w ∈ upperHalfPlane K₀ K) :
    theta ρ₂ (pmoebius K₀ n a) (pmoebius K₀ n b) (pmoebius K₀ n z₀) (pmoebius K₀ n w) = theta ρ₁ a b z₀ w := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_theta_pmoebius_eq_theta_of_mulEquiv_of_apply_eq_conj.solution
