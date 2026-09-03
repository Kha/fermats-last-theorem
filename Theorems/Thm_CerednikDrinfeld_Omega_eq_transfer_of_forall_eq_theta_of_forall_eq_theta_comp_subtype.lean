import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Mathlib.GroupTheory.Transfer
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_eq_transfer_of_forall_eq_theta_of_forall_eq_theta_comp_subtype

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega hiding exists_monoidHom_fracAct_thetaMer_eq open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.eq_transfer_of_forall_eq_theta_of_forall_eq_theta_comp_subtype
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (Γ' : Subgroup G) [Γ'.FiniteIndex]
    {a' b' z₀ : K} (ha' : a' ∈ upperHalfPlane K₀ K) (hb' : b' ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b' ≠ z₀)
    (c' : ↥Γ' →* Kˣ) (hc' : ∀ β : ↥Γ', ((c' β : Kˣ) : K) = theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ β) z₀))
    (c : G →* Kˣ) (hc : ∀ β : G, ((c β : Kˣ) : K) = theta ρ a' b' z₀ (pmoebius K₀ (ρ β) z₀)) :
    c = MonoidHom.transfer c' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_eq_transfer_of_forall_eq_theta_of_forall_eq_theta_comp_subtype.solution
