import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_isZero_H1_and_natCard_H2_and_span_map_of_iso

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.isZero_H1_and_natCard_H2_and_span_map_of_iso
    {G : Type} [Group G] (A B : Rep ℤ G) (e : A ≅ B) (u : groupCohomology A 2)
    (h1 : ∀ S : Subgroup G, CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1))
    (h2 : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype A) 2) = Fintype.card S)
    (h3 : ∀ S : Subgroup G,
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2).hom u} = ⊤) :
    (∀ S : Subgroup G, CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1)) ∧
    (∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype B) 2) = Fintype.card S) ∧
    (∀ S : Subgroup G,
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype B)) 2).hom
        ((groupCohomology.map (MonoidHom.id G) e.hom 2).hom u)} = ⊤) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_isZero_H1_and_natCard_H2_and_span_map_of_iso.solution
