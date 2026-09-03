import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_continuous_of_mem_holOn

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.continuous_of_mem_holOn
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {S : Set K} {g : ↥S → K} (hg : g ∈ holOn K S) :
    Continuous g := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_continuous_of_mem_holOn.solution
