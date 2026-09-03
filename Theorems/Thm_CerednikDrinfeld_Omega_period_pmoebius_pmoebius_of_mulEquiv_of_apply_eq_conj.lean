import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_period_pmoebius_pmoebius_of_mulEquiv_of_apply_eq_conj

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld.Omega~crossRatio_pmoebius"

theorem CerednikDrinfeld.Omega.period_pmoebius_pmoebius_of_mulEquiv_of_apply_eq_conj
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K] [TopologicalSpace K]
    {G₁ G₂ : Type*} [Group G₁] [Group G₂] (ρ₁ : G₁ →* PGL(2, K₀)) (ρ₂ : G₂ →* PGL(2, K₀))
    (e : G₁ ≃* G₂) (n : PGL(2, K₀)) (he : ∀ g : G₁, ρ₂ (e g) = n * ρ₁ g * n⁻¹)
    {a z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (α β : G₁) :
    period ρ₂ (pmoebius K₀ n a) (pmoebius K₀ n z₀) (e α) (e β) = period ρ₁ a z₀ α β := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_period_pmoebius_pmoebius_of_mulEquiv_of_apply_eq_conj.solution
