import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_monoidHom_fracAct_thetaMer_eq

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega hiding exists_isThetaPair_thetaMer_eq_mk thetaMer_mul_algebraMap_eq_of_isThetaPair thetaMultipliable_of_isDiscrete_of_isExhausted exists_monoidHom_isAutomorphicWithMultiplier_theta open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.exists_monoidHom_fracAct_thetaMer_eq
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) :
    ∃ c : G →* Kˣ,
      (∀ β : G, ((c β : Kˣ) : K) = theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀)) ∧
      ∀ γ : G, Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ γ) (thetaMer ϖ ρ a b z₀) =
        algebraMap K (merField ϖ) (((c γ)⁻¹ : Kˣ) : K) * thetaMer ϖ ρ a b z₀ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_monoidHom_fracAct_thetaMer_eq.solution
