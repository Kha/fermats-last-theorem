import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld.Omega~finite_setOf_pmoebius_mem_affinoid~exists_monoidHom_isAutomorphicWithMultiplier_theta~exists_mem_holOn_hasProd_evalAt~eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt~continuous_of_mem_holOn"

theorem CerednikDrinfeld.Omega.exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (α : G) :
    ∃ U : ↥(holRing ϖ), IsUnit U ∧
      algebraMap ↥(holRing ϖ) (merField ϖ) U = thetaMer ϖ ρ a (pmoebius K₀ (ρ α) a) z₀ ∧
      (∀ z : ↥(upperHalfPlane K₀ K), (¬ ∃ γ : G, pmoebius K₀ (ρ γ) a = (z : K)) →
        (U : ↥(upperHalfPlane K₀ K) → K) z = theta ρ a (pmoebius K₀ (ρ α) a) z₀ (z : K)) ∧
      ∀ (β : G) (z : ↥(upperHalfPlane K₀ K)),
        (U : ↥(upperHalfPlane K₀ K) → K) ((ρ β) • z) = period ρ a z₀ α β * (U : ↥(upperHalfPlane K₀ K) → K) z := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul.solution
