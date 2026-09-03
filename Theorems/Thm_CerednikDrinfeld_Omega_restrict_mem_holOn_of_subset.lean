import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Omega_restrict_mem_holOn_of_subset

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.restrict_mem_holOn_of_subset
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {S T : Set K} (hTS : T ⊆ S) {f : ↥S → K} (hf : f ∈ holOn K S) :
    (fun z : ↥T => f ⟨(z : K), hTS z.2⟩) ∈ holOn K T := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_restrict_mem_holOn_of_subset.solution
