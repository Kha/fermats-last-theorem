import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_finrank_invariants_comp_eq_of_rat

set_option autoImplicit false
theorem Rep.finrank_invariants_comp_eq_of_rat {G : Type} [Group G] [Finite G]
    {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (τ : Representation ℚ G V)
    {L : Rep ℤ G} [Module.Finite ℤ L] [Module.Free ℤ L]
    (i : L →+ V) (hi : Function.Injective i) (hiG : ∀ (g : G) (x : L), i (L.ρ g x) = τ g (i x))
    (hfull : Submodule.span ℚ (Set.range i) = ⊤) (H : Subgroup G) :
    Module.finrank ℚ (Representation.invariants (τ.comp H.subtype)) =
      Module.finrank ℤ (groupCohomology (Rep.res H.subtype L) 0) := by p2m_exact_reverting @_root_.P2MW.S_Rep_finrank_invariants_comp_eq_of_rat.solution
