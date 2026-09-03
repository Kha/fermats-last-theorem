import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_nonempty_invariants_coind_linearEquiv_invariants

set_option autoImplicit false

universe u

open CategoryTheory
theorem Rep.nonempty_invariants_coind_linearEquiv_invariants {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) (N : Rep.{u} k S) :
    Nonempty ((Rep.coind S.subtype N).ρ.invariants ≃ₗ[k] N.ρ.invariants) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_invariants_coind_linearEquiv_invariants.solution
