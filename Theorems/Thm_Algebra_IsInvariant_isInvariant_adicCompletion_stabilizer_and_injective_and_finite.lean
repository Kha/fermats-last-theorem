import Mathlib
import Definitions.Def_AdicCompletionGaloisAction
import P2M.Util
import P2M.Sol.S_Algebra_IsInvariant_isInvariant_adicCompletion_stabilizer_and_injective_and_finite
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp] AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul

set_option autoImplicit false

open scoped Pointwise
open scoped AdicCompletion.GaloisAction

theorem Algebra.IsInvariant.isInvariant_adicCompletion_stabilizer_and_injective_and_finite
    {O : Type*} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    {C : Type*} [CommRing C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G C] [SMulCommClass G O C]
    [Algebra.IsInvariant O C G]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (IsLocalRing.maximalIdeal O)] :
    Algebra.IsInvariant (AdicCompletion (IsLocalRing.maximalIdeal O) O) (AdicCompletion 𝔫 C)
        (MulAction.stabilizer G 𝔫) ∧
    Function.Injective
        (algebraMap (AdicCompletion (IsLocalRing.maximalIdeal O) O) (AdicCompletion 𝔫 C)) ∧
    Module.Finite (AdicCompletion (IsLocalRing.maximalIdeal O) O) (AdicCompletion 𝔫 C) ∧
    (𝔫.map (algebraMap C (AdicCompletion 𝔫 C))).inertia (MulAction.stabilizer G 𝔫) =
        (𝔫.inertia G).subgroupOf (MulAction.stabilizer G 𝔫) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsInvariant_isInvariant_adicCompletion_stabilizer_and_injective_and_finite.solution
