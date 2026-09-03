import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Mathlib.GroupTheory.Transfer
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_prod_theta_comp_subtype_pmoebius_eq_mul_theta_and_prod_fracAct_thetaMer_eq

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.prod_theta_comp_subtype_pmoebius_eq_mul_theta_and_prod_fracAct_thetaMer_eq
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (Γ' : Subgroup G) [Fintype (G ⧸ Γ')] (s : G ⧸ Γ' → G) (hs : ∀ q : G ⧸ Γ', (QuotientGroup.mk (s q) : G ⧸ Γ') = q)
    {a' b' z₀ : K} (ha' : a' ∈ upperHalfPlane K₀ K) (hb' : b' ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b' ≠ z₀) :
    (∀ z ∈ upperHalfPlane K₀ K,
        ∏ q : G ⧸ Γ', theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ (s q))⁻¹ z) =
          (∏ q : G ⧸ Γ', theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ (s q))⁻¹ z₀)) * theta ρ a' b' z₀ z) ∧
      ∏ q : G ⧸ Γ', Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ (s q)) (thetaMer ϖ (ρ.comp Γ'.subtype) a' b' z₀) =
        algebraMap K (merField ϖ) (∏ q : G ⧸ Γ', theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ (s q))⁻¹ z₀)) *
          thetaMer ϖ ρ a' b' z₀ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_prod_theta_comp_subtype_pmoebius_eq_mul_theta_and_prod_fracAct_thetaMer_eq.solution
