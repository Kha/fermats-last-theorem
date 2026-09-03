import Mathlib
import Definitions.Def_GroupCohomology_CupProduct
import P2M.Util
import P2M.Sol.S_groupCohomology_cupCochain_coind_apply_one

set_option autoImplicit false

universe u

open CategoryTheory
open groupCohomology
theorem groupCohomology.cupCochain_coind_apply_one
    {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)
    {A B N : Rep.{u} k S} (φ : A →ₗ[k] B →ₗ[k] N)
    (x : G → Rep.coind S.subtype A) (y : G → Rep.coind S.subtype B) (s t : S) :
    φ ((x s : G → A) 1) (((Rep.coind S.subtype B).ρ s (y t) : G → B) 1)
      = cupCochain φ (fun u : S => (x u : G → A) 1) (fun u : S => (y u : G → B) 1) (s, t) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_cupCochain_coind_apply_one.solution
