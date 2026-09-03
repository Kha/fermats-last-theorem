import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_natCard_eq_and_span_map_eq_top_of_addOrderOf_eq_natCard
set_option autoImplicit false
open CategoryTheory

theorem groupCohomology.natCard_eq_and_span_map_eq_top_of_addOrderOf_eq_natCard
    {G : Type} [Group G] [Finite G]
    (X : Rep ℤ G) (u : groupCohomology X 2) (hu : addOrderOf u = Nat.card G)
    (h5 : ∀ (S : Subgroup G) [Fintype S], Finite (groupCohomology (Rep.res S.subtype X) 2) ∧
      Nat.card (groupCohomology (Rep.res S.subtype X) 2) ≤ Fintype.card S)
    (cor : ∀ S : Subgroup G, groupCohomology (Rep.res S.subtype X) 2 →ₗ[ℤ] groupCohomology X 2)
    (hcor : ∀ (S : Subgroup G) (x : groupCohomology X 2),
      cor S ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) 2).hom x) = S.index • x) :
    (∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype X) 2) = Fintype.card S) ∧
    (∀ S : Subgroup G, Submodule.span ℤ
      {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) 2).hom u} = ⊤) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_natCard_eq_and_span_map_eq_top_of_addOrderOf_eq_natCard.solution
