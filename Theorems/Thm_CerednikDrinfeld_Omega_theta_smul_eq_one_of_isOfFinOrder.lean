import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.OrderOfElement
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_theta_smul_eq_one_of_isOfFinOrder

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega hiding exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.theta_smul_eq_one_of_isOfFinOrder
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (α : G) (hα : IsOfFinOrder α)
    {p w z : K} (hp : p ∈ upperHalfPlane K₀ K) (hw : w ∈ upperHalfPlane K₀ K) (hz : z ∈ upperHalfPlane K₀ K)
    (hwp : ∀ γ : G, pmoebius K₀ (ρ γ) p ≠ w) (hzp : ∀ γ : G, pmoebius K₀ (ρ γ) p ≠ z) :
    theta ρ p (pmoebius K₀ (ρ α) p) w z = 1 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_theta_smul_eq_one_of_isOfFinOrder.solution
