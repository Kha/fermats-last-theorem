import Mathlib
import Definitions.Def_GroupCohomology_CupProduct
import P2M.Util
namespace P2MW.S_groupCohomology_cupCochain_coind_apply_one

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

open CategoryTheory
open groupCohomology

theorem solution
    {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)
    {A B N : Rep.{u} k S} (φ : A →ₗ[k] B →ₗ[k] N)
    (x : G → Rep.coind S.subtype A) (y : G → Rep.coind S.subtype B) (s t : S) :
    φ ((x s : G → A) 1) (((Rep.coind S.subtype B).ρ s (y t) : G → B) 1)
      = cupCochain φ (fun u : S => (x u : G → A) 1) (fun u : S => (y u : G → B) 1) (s, t) := by
  rw [cupCochain_apply]
  congr 1
  show ((y t : Rep.coind S.subtype B) : G → B) (1 * (s : G)) = B.ρ s (((y t : Rep.coind S.subtype B) : G → B) 1)
  rw [one_mul, ← mul_one (s : G)]
  exact (y t).2 s 1
