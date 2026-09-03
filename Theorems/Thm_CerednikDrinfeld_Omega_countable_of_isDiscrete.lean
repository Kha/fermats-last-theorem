import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_countable_of_isDiscrete

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.countable_of_isDiscrete
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ) :
    Countable G := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_countable_of_isDiscrete.solution
