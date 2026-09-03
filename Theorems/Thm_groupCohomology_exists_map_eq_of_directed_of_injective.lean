import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_map_eq_of_directed_of_injective

set_option autoImplicit false

universe u v

open CategoryTheory

theorem groupCohomology.exists_map_eq_of_directed_of_injective
    {k G : Type u} [CommRing k] [Group G] [Finite G]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    {B : Rep k G} (A : I → Rep k G) (ι : ∀ i, A i ⟶ B) (hι : ∀ i, Function.Injective (ι i).hom)
    (hmono : ∀ i j, i ≤ j → Set.range (ι i).hom ⊆ Set.range (ι j).hom)
    (hcov : ∀ b : B, ∃ i, b ∈ Set.range (ι i).hom)
    (n : ℕ) (x : groupCohomology B n) (i₀ : I) :
    ∃ i, i₀ ≤ i ∧ ∃ y : groupCohomology (A i) n, (groupCohomology.map (MonoidHom.id G) (ι i) n).hom y = x := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_map_eq_of_directed_of_injective.solution
