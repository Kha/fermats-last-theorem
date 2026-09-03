import Mathlib
import P2M.Util
import P2M.Sol.S_IsConstructible_isClosed_of_forall_specializes_mem_of_jacobsonSpace

set_option autoImplicit false

universe u

open Topology

theorem IsConstructible.isClosed_of_forall_specializes_mem_of_jacobsonSpace
    {X : Type u} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X] [JacobsonSpace X]
    {C : Set X} (hC : IsConstructible C)
    (h : ∀ x ∈ C, ∀ y : X, x ⤳ y → IsClosed ({y} : Set X) → y ∈ C) :
    IsClosed C := by p2m_exact_reverting @_root_.P2MW.S_IsConstructible_isClosed_of_forall_specializes_mem_of_jacobsonSpace.solution
