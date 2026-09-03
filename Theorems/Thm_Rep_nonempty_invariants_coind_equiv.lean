import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_nonempty_invariants_coind_equiv

set_option autoImplicit false
open CategoryTheory Module
theorem Rep.nonempty_invariants_coind_equiv
    {k G : Type} [CommRing k] [Group G] (H : Subgroup G) (N : Rep.{0} k ↥H) :
    Nonempty ((Rep.coind H.subtype N).ρ.invariants ≃ₗ[k] N.ρ.invariants) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_invariants_coind_equiv.solution
