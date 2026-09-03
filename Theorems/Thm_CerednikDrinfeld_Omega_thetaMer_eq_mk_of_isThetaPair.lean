import Definitions.Def_CerednikDrinfeld_ThetaMer
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_thetaMer_eq_mk_of_isThetaPair

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.thetaMer_eq_mk_of_isThetaPair
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (a b z₀ : K)
    (F H : ↥(holRing ϖ)) (h : IsThetaPair ϖ ρ a b z₀ F H) :
    thetaMer ϖ ρ a b z₀ = Localization.mk F ⟨H, h.1⟩ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_thetaMer_eq_mk_of_isThetaPair.solution
