import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_exists_hom_injective_finiteIndex_of_rat

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.exists_hom_injective_finiteIndex_of_rat {G : Type} [Group G] [Finite G]
    {V : Type} [AddCommGroup V] [Module ℚ V] (τ : Representation ℚ G V)
    {L L' : Rep ℤ G} [Module.Finite ℤ L] [Module.Finite ℤ L']
    (i : L →+ V) (hi : Function.Injective i) (hiG : ∀ (g : G) (x : L), i (L.ρ g x) = τ g (i x))
    (i' : L' →+ V) (hi' : Function.Injective i') (hi'G : ∀ (g : G) (x : L'), i' (L'.ρ g x) = τ g (i' x))
    (hfull : Submodule.span ℚ (Set.range i) = ⊤) (hfull' : Submodule.span ℚ (Set.range i') = ⊤) :
    ∃ f : L ⟶ L', Function.Injective f.hom ∧ (f.hom : L →+ L').range.FiniteIndex := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_hom_injective_finiteIndex_of_rat.solution
