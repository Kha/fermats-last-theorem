import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_coind_cocycles1_mem_coboundaries1_of_eval_one_mem_coboundaries1

set_option autoImplicit false

universe u

open CategoryTheory
theorem groupCohomology.coind_cocycles1_mem_coboundaries1_of_eval_one_mem_coboundaries1 {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) (N : Rep.{u} k S)
    (c : groupCohomology.cocycles₁ (Rep.coind S.subtype N))
    (hc : (fun s : S => ((c (s : G) : Rep.coind S.subtype N) : G → N) 1) ∈ groupCohomology.coboundaries₁ N) :
    (c : G → Rep.coind S.subtype N) ∈ groupCohomology.coboundaries₁ (Rep.coind S.subtype N) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_coind_cocycles1_mem_coboundaries1_of_eval_one_mem_coboundaries1.solution
