import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_finrank_fractionRing_adicCompletion_tensorProduct_eq

set_option autoImplicit false

universe u v

open IsLocalRing in
open scoped TensorProduct in

theorem IsLocalRing.finrank_fractionRing_adicCompletion_tensorProduct_eq
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
    Module.finrank L M = Module.finrank K₁ K := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_finrank_fractionRing_adicCompletion_tensorProduct_eq.solution
