import Mathlib
import P2M.Util
namespace P2MW.S_Bialgebra_existsUnique_counit_apply_eq_one_of_completeOrthogonalIdempotents

set_option autoImplicit false

universe u v

theorem hensSplit_isIdempotentElem_eq_zero_or_one {R : Type u} [CommRing R] [IsLocalRing R] {a : R}
    (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
  · right
    exact h.mul_left_cancel (by rw [mul_one]; exact ha.eq)
  · left
    have : (1 - a) * a = (1 - a) * 0 := by rw [mul_zero, sub_mul, one_mul, ha.eq, sub_self]
    exact h.mul_left_cancel this

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R]
    {H : Type v} [CommRing H] [Bialgebra R H]
    {ι : Type} [Fintype ι] (e : ι → H) (he : CompleteOrthogonalIdempotents e) :
    ∃! i : ι, Coalgebra.counit (R := R) (e i) = 1 := by
  classical
  let ε : H →ₐ[R] R := Bialgebra.counitAlgHom R H
  have hε : ∀ x, ε x = Coalgebra.counit x := fun x => Bialgebra.counitAlgHom_apply R H x
  have h01 : ∀ i, ε (e i) = 0 ∨ ε (e i) = 1 := fun i =>
    hensSplit_isIdempotentElem_eq_zero_or_one ((he.idem i).map ε)
  have hsum : ∑ i, ε (e i) = 1 := by rw [← map_sum, he.complete, map_one]
  have hex : ∃ i, ε (e i) = 1 := by
    by_contra h
    have h0 : ∀ i, ε (e i) = 0 := fun i => (h01 i).resolve_right (fun hi => h ⟨i, hi⟩)
    have : ∑ i, ε (e i) = 0 := Finset.sum_eq_zero fun i _ => h0 i
    rw [hsum] at this
    exact one_ne_zero this
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ?_, fun j hj => ?_⟩
  · show Coalgebra.counit (e i) = 1
    rw [← hε]; exact hi
  have hj' : ε (e j) = 1 := by rw [hε]; exact hj
  by_contra hne
  have h0 : e j * e i = 0 := he.ortho hne
  have h2 : ε (e j * e i) = 1 := by rw [map_mul, hi, hj', one_mul]
  rw [h0, map_zero] at h2
  exact zero_ne_one h2
