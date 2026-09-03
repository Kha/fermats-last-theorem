import Mathlib
import P2M.Util
namespace P2MW.S_ValuationSubring_addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder

set_option autoImplicit false

universe u v

open AddMonoidAlgebra

theorem solution
    {L : Type u} [Field L] (A : ValuationSubring L)
    {G : Type v} [AddMonoid G] (hG : ∀ g : G, IsOfFinAddOrder g)
    (χ : AddMonoidAlgebra A G →ₐ[A] L) :
    (∀ x, χ x ∈ A) ∧ ∃ χA : AddMonoidAlgebra A G →ₐ[A] A, ∀ x, (χA x : L) = χ x := by
  have hsingle : ∀ g : G, χ (single g 1) ∈ A := by
    intro g
    obtain ⟨n, hn, hng⟩ := (hG g).exists_nsmul_eq_zero
    have hpow : χ (single g 1) ^ n = 1 := by
      rw [← map_pow, AddMonoidAlgebra.single_pow, hng, one_pow]
      exact map_one χ
    have hint : IsIntegral A (χ (single g 1)) :=
      IsIntegral.of_pow hn (by rw [hpow]; exact isIntegral_one)
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := L)).mp hint
    rw [← hy]
    exact y.2
  have hall : ∀ x, χ x ∈ A := by
    intro x
    induction x using AddMonoidAlgebra.induction_on with
    | of g => simpa only [AddMonoidAlgebra.of_apply, toAdd_ofAdd] using hsingle g
    | add f g hf hg => rw [map_add]; exact A.add_mem _ _ hf hg
    | smul r f hf =>
      rw [map_smul, Algebra.smul_def]
      exact A.mul_mem _ _ r.2 hf
  refine ⟨hall, ?_⟩
  refine ⟨{ toFun := fun x => ⟨χ x, hall x⟩, map_one' := ?_, map_mul' := ?_, map_zero' := ?_,
            map_add' := ?_, commutes' := ?_ }, fun x => rfl⟩
  · exact Subtype.ext (map_one χ)
  · intro x y; exact Subtype.ext (map_mul χ x y)
  · exact Subtype.ext (map_zero χ)
  · intro x y; exact Subtype.ext (map_add χ x y)
  · intro a; exact Subtype.ext (χ.commutes a)
