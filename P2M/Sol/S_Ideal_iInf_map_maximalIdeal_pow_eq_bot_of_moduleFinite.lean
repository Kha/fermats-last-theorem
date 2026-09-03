import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
namespace P2MW.S_Ideal_iInf_map_maximalIdeal_pow_eq_bot_of_moduleFinite

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem solution
    (S : Type*) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (C : Type*) [CommRing C] [Algebra S C] [Module.Finite S C] [Nontrivial C] :
    ⨅ n : ℕ, (maximalIdeal S ^ n).map (algebraMap S C) = ⊥ := by
  have h := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (I := maximalIdeal S) (M := C)
    (maximalIdeal.isMaximal S).ne_top
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ (⨅ i : ℕ, (maximalIdeal S ^ i • ⊤ : Submodule S C)) := by
    rw [Submodule.mem_iInf]
    intro i
    rw [Ideal.smul_top_eq_map]
    exact (Submodule.mem_iInf _).mp hx i
  rw [h] at hx'
  exact hx'
