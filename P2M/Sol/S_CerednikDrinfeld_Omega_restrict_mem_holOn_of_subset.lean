import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_Omega_restrict_mem_holOn_of_subset

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {S T : Set K} (hTS : T ⊆ S) {f : ↥S → K} (hf : f ∈ holOn K S) :
    (fun z : ↥T => f ⟨(z : K), hTS z.2⟩) ∈ holOn K T := by
  rw [mem_holOn_iff] at hf ⊢
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf
  exact ⟨r, fun k z hz => hr k z (hTS hz), ⟨b, fun k z => hb k ⟨(z : K), hTS z.2⟩⟩,
    hlim.comp (fun z : ↥T => (⟨(z : K), hTS z.2⟩ : ↥S))⟩
