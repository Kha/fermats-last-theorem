import Mathlib
import Definitions.Def_AdicCompletionGaloisAction
import P2M.Util
import P2M.Sol.S_AdicCompletion_isField_localization_atPrime_of_not_isMaximal_of_isSeparable
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp] AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul

set_option autoImplicit false

open IsLocalRing
open scoped AdicCompletion.GaloisAction

theorem AdicCompletion.isField_localization_atPrime_of_not_isMaximal_of_isSeparable
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {C : Type} [CommRing C] [IsDomain C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    (K L : Type) [Field K] [Field L] [Algebra O K] [IsFractionRing O K] [Algebra C L] [IsFractionRing C L]
    [Algebra K L] [Algebra O L] [IsScalarTower O K L] [IsScalarTower O C L] [Algebra.IsSeparable K L]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)]
    (𝔓 : Ideal (AdicCompletion 𝔫 C)) [𝔓.IsPrime] (h𝔓 : ¬ 𝔓.IsMaximal) :
    IsField (Localization.AtPrime 𝔓) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_isField_localization_atPrime_of_not_isMaximal_of_isSeparable.solution
