import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_isThetaPair_thetaMer_eq_mk

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld.Omega~exists_holRing_div_eq_theta"

theorem CerednikDrinfeld.Omega.exists_isThetaPair_thetaMer_eq_mk
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) :
    ∃ (F H : ↥(holRing ϖ)) (h : IsThetaPair ϖ ρ a b z₀ F H),
      thetaMer ϖ ρ a b z₀ = Localization.mk F ⟨H, h.1⟩ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_isThetaPair_thetaMer_eq_mk.solution
