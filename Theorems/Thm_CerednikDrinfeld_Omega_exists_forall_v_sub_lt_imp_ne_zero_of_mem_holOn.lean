import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_exists_forall_v_sub_lt_imp_ne_zero_of_mem_holOn

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_forall_v_sub_lt_imp_ne_zero_of_mem_holOn
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {S : Set K} {f : ↥S → K} (hf : f ∈ holOn K S) (z₀ : ↥S) (hz₀ : f z₀ ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ z : ↥S, Valued.v ((z : K) - (z₀ : K)) < Valued.v c → f z ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_forall_v_sub_lt_imp_ne_zero_of_mem_holOn.solution
