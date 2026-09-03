import Mathlib
import P2M.Util
import P2M.Sol.S_Topology_IsConstructible_mem_of_mem_closure_of_forall_specializes

set_option autoImplicit false

open Topology

universe u

theorem Topology.IsConstructible.mem_of_mem_closure_of_forall_specializes
    {X : Type u} [TopologicalSpace X] {s : Set X} (hs : Topology.IsConstructible s)
    {x : X} (hx : x ∈ closure s) (hgen : ∀ y ∈ s, x ⤳ y) : x ∈ s := by p2m_exact_reverting @_root_.P2MW.S_Topology_IsConstructible_mem_of_mem_closure_of_forall_specializes.solution
