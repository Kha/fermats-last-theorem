import Mathlib
import Theorems.Thm_Algebra_finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite
import P2M.Util
namespace P2MW.S_IsLocalRing_finrank_fractionRing_adicCompletion_tensorProduct_eq

set_option autoImplicit false

universe u v

open IsLocalRing
open scoped TensorProduct

theorem solution
    {O : Type u} {C : Type v} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsLocalRing O]
    [CommRing C] [IsDomain C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    (K₁ K : Type*) [Field K₁] [Field K] [Algebra O K₁] [IsFractionRing O K₁]
    [Algebra C K] [IsFractionRing C K] [Algebra K₁ K] [Algebra O K]
    [IsScalarTower O C K] [IsScalarTower O K₁ K]
    [IsDomain (AdicCompletion (maximalIdeal O) O)] [IsDomain ((AdicCompletion (maximalIdeal O) O) ⊗[O] C)]
    (L M : Type*) [Field L] [Field M]
    [Algebra (AdicCompletion (maximalIdeal O) O) L] [IsFractionRing (AdicCompletion (maximalIdeal O) O) L]
    [Algebra ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) M] [IsFractionRing ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) M]
    [Algebra L M] [Algebra (AdicCompletion (maximalIdeal O) O) M]
    [IsScalarTower (AdicCompletion (maximalIdeal O) O) ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) M]
    [IsScalarTower (AdicCompletion (maximalIdeal O) O) L M] :
    Module.finrank L M = Module.finrank K₁ K := by

  have h1 := Algebra.finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite
    (A := AdicCompletion (maximalIdeal O) O) (B := (AdicCompletion (maximalIdeal O) O) ⊗[O] C)
    L (F := L) (F' := M) (algebraMap L M)
    (fun a => ((IsScalarTower.algebraMap_apply (AdicCompletion (maximalIdeal O) O)
      ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) M a).symm.trans
      (IsScalarTower.algebraMap_apply (AdicCompletion (maximalIdeal O) O) L M a)))
  have hA : (algebraMap L M).toAlgebra = ‹Algebra L M› := Algebra.algebra_ext _ _ fun _ => rfl
  rw [hA] at h1

  have h2 := Algebra.finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite
    (A := O) (B := C) K₁ (F := K₁) (F' := K) (algebraMap K₁ K)
    (fun a => ((IsScalarTower.algebraMap_apply O C K a).symm.trans (IsScalarTower.algebraMap_apply O K₁ K a)))
  have hB : (algebraMap K₁ K).toAlgebra = ‹Algebra K₁ K› := Algebra.algebra_ext _ _ fun _ => rfl
  rw [hB] at h2
  rw [← h1, ← h2]

  letI algOL : Algebra O L := ((algebraMap (AdicCompletion (maximalIdeal O) O) L).comp
    (algebraMap O (AdicCompletion (maximalIdeal O) O))).toAlgebra
  haveI : IsScalarTower O (AdicCompletion (maximalIdeal O) O) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e3 : L ⊗[AdicCompletion (maximalIdeal O) O] ((AdicCompletion (maximalIdeal O) O) ⊗[O] C) ≃ₗ[L] L ⊗[O] C :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange O (AdicCompletion (maximalIdeal O) O) L L C
  rw [LinearEquiv.finrank_eq e3]

  have hinjO : Function.Injective (algebraMap O L) := by
    show Function.Injective ((algebraMap (AdicCompletion (maximalIdeal O) O) L).comp
      (algebraMap O (AdicCompletion (maximalIdeal O) O)))
    exact (IsFractionRing.injective (AdicCompletion (maximalIdeal O) O) L).comp
      (AdicCompletion.of_injective (maximalIdeal O) O)
  letI algKL : Algebra K₁ L := (IsFractionRing.lift (K := K₁) hinjO).toAlgebra
  haveI : IsScalarTower O K₁ L :=
    IsScalarTower.of_algebraMap_eq fun o => (IsFractionRing.lift_algebraMap hinjO o).symm
  let e4 : L ⊗[K₁] (K₁ ⊗[O] C) ≃ₗ[L] L ⊗[O] C := TensorProduct.AlgebraTensorModule.cancelBaseChange O K₁ L L C
  rw [← LinearEquiv.finrank_eq e4, Module.finrank_baseChange]
