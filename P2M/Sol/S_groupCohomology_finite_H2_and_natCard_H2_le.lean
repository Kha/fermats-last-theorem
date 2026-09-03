import Mathlib
import Theorems.Thm_groupCohomology_H2res_comp_H2inf_eq_zero
import Theorems.Thm_groupCohomology_exists_H2inf_eq_of_H2res_eq_zero
import P2M.Util
namespace P2MW.S_groupCohomology_finite_H2_and_natCard_H2_le

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology Rep

theorem solution
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Subsingleton (H1 (Rep.res S.subtype A))]
    [Finite (H2 (A.quotientToInvariants S))] [Finite (H2 (Rep.res S.subtype A))] :
    Finite (H2 A) ∧
      Nat.card (H2 A) ≤ Nat.card (H2 (A.quotientToInvariants S)) * Nat.card (H2 (Rep.res S.subtype A)) := by
  set inf := (groupCohomology.map (A := A.quotientToInvariants S) (B := A)
        (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2).hom
  set res := (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2).hom
  have hexact : LinearMap.range inf = LinearMap.ker res := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      have h := congrArg (fun f => (ModuleCat.Hom.hom f) y) (H2res_comp_H2inf_eq_zero A S)
      simpa [ModuleCat.hom_comp] using h
    · intro x hx
      obtain ⟨y, hy⟩ := exists_H2inf_eq_of_H2res_eq_zero A S x (LinearMap.mem_ker.1 hx)
      exact ⟨y, hy⟩
  haveI : Finite (LinearMap.ker res) := by
    rw [← hexact]; exact Finite.of_surjective _ inf.surjective_rangeRestrict
  haveI : Finite (LinearMap.range res) := Finite.Set.subset _ (Set.subset_univ _)
  have hN : Nat.card (H2 A) = Nat.card (LinearMap.ker res) * Nat.card (LinearMap.range res) := by
    rw [← Nat.card_congr res.quotKerEquivRange.toEquiv, mul_comm]
    exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker res).toAddSubgroup
  have hfin : Finite (H2 A) :=
    Nat.finite_of_card_ne_zero (by rw [hN]; exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')
  refine ⟨hfin, ?_⟩
  rw [hN, ← hexact]
  exact Nat.mul_le_mul (Nat.card_le_card_of_surjective _ inf.surjective_rangeRestrict)
    (Nat.card_le_card_of_injective _ (LinearMap.range res).injective_subtype)
