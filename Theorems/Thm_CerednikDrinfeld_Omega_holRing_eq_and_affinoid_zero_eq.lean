import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_holRing_eq_and_affinoid_zero_eq

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.holRing_eq_and_affinoid_zero_eq
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ ϖ' : PseudoUniformizer K₀ K) : holRing ϖ = holRing ϖ' ∧ affinoid ϖ 0 = affinoid ϖ' 0 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_holRing_eq_and_affinoid_zero_eq.solution
