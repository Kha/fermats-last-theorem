import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import P2M.Util
namespace P2MW.S_IharaLemma_isPrecomplete_of_finite

set_option autoImplicit false

theorem solution {R : Type*} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite (I := I) (M := M) y
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
  | tmul r m =>
    obtain ⟨s, rfl⟩ := AdicCompletion.of_surjective I R r
    refine ⟨s • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    exact (algebraMap_smul (AdicCompletion I R) s (AdicCompletion.of I M m)).symm
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
