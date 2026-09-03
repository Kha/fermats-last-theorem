import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_exists_injective_equivariant_of_quadraticRelation_of_isArtinianRing_of_isReduced

set_option autoImplicit false

theorem Representation.exists_injective_equivariant_of_quadraticRelation_of_isArtinianRing_of_isReduced
    {k : Type} [CommRing k] [IsArtinianRing k] [IsReduced k] [Algebra ℚ k]
    {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Free k V] [Module.Finite k V] (hV : Module.finrank k V = 2)
    (ρV : G →* Module.End k V) (hspan : Submodule.span k (Set.range ⇑ρV) = ⊤)
    {M : Type} [AddCommGroup M] [Module k M] [Module.Finite k M]
    (hfaith : ∀ x : k, (∀ m : M, x • m = 0) → x = 0)
    (ρM : G →* Module.End k M) (d : G →* kˣ)
    (hrel : ∀ g : G,
      ρM g * ρM g - (LinearMap.trace k V (ρV g)) • ρM g + ((d g : kˣ) : k) • (1 : Module.End k M) = 0) :
    ∃ j : V →ₗ[k] M, Function.Injective j ∧ ∀ (g : G) (v : V), j (ρV g v) = ρM g (j v) := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_injective_equivariant_of_quadraticRelation_of_isArtinianRing_of_isReduced.solution
