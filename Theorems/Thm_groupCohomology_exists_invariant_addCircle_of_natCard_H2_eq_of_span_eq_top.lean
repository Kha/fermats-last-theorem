import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_invariant_addCircle_of_natCard_H2_eq_of_span_eq_top
set_option autoImplicit false
open CategoryTheory in

theorem groupCohomology.exists_invariant_addCircle_of_natCard_H2_eq_of_span_eq_top
    {G : Type} [Group G] [Fintype G] (X : Rep ℤ G) (u : groupCohomology X 2)
    (hcard : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype X) 2) = Fintype.card S)
    (hspan : ∀ S : Subgroup G, Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) 2).hom u} = ⊤) :
    ∃ (invG : groupCohomology X 2 →+ AddCircle (1 : ℚ))
      (inv : ∀ H : Subgroup G, groupCohomology (Rep.res H.subtype X) 2 →+ AddCircle (1 : ℚ)),
      Function.Injective invG ∧ (∀ H : Subgroup G, Function.Injective (inv H)) ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card G • t = 0) ∧
      (∀ (H : Subgroup G) (t : AddCircle (1 : ℚ)), t ∈ (inv H).range ↔ Nat.card ↥H • t = 0) ∧
      (∀ (H : Subgroup G) (x : groupCohomology X 2),
        inv H ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype X)) 2).hom x) = H.index • invG x) ∧
      invG u = (((1 : ℚ) / (Nat.card G : ℚ) : ℚ) : AddCircle (1 : ℚ)) ∧
      (∀ H : Subgroup G, inv H ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype X)) 2).hom u) =
        (((1 : ℚ) / (Nat.card ↥H : ℚ) : ℚ) : AddCircle (1 : ℚ))) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_invariant_addCircle_of_natCard_H2_eq_of_span_eq_top.solution
