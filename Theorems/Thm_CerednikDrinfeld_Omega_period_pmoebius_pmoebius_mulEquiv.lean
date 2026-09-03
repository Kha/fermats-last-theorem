import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_period_pmoebius_pmoebius_mulEquiv

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.period_pmoebius_pmoebius_mulEquiv
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K] [TopologicalSpace K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) (φ : G ≃* G) (n : PGL(2, K₀))
    (hφ : ∀ g : G, ρ (φ g) = n * ρ g * n⁻¹)
    {a z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (α β : G) :
    period ρ (pmoebius K₀ n a) (pmoebius K₀ n z₀) (φ α) (φ β) = period ρ a z₀ α β := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_period_pmoebius_pmoebius_mulEquiv.solution
