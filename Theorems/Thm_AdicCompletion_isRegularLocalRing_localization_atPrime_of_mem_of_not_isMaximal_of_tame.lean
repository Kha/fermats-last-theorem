import Mathlib
import Definitions.Def_AdicCompletionGaloisAction
import P2M.Util
import P2M.Sol.S_AdicCompletion_isRegularLocalRing_localization_atPrime_of_mem_of_not_isMaximal_of_tame
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp] AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul

set_option autoImplicit false

open IsLocalRing
open scoped Pointwise
open scoped AdicCompletion.GaloisAction

theorem AdicCompletion.isRegularLocalRing_localization_atPrime_of_mem_of_not_isMaximal_of_tame
    {O : Type} [CommRing O] [IsRegularLocalRing O]
    (ϖ s : O) (hmaxO : maximalIdeal O = Ideal.span {ϖ, s}) (hdimO : ringKrullDim O = 2)
    (e : ℕ) (he : 0 < e) (heO : IsUnit (e : O))
    {C : Type} [CommRing C] [IsDomain C] [IsIntegrallyClosed C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    {G : Type} [Group G] [Finite G] [MulSemiringAction G C] [SMulCommClass G O C] [FaithfulSMul G C]
    [Algebra.IsInvariant O C G]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)]
    (hI : Nat.card ↥((𝔫.inertia G).subgroupOf (MulAction.stabilizer G 𝔫)) = e)
    (𝔭 : Ideal (AdicCompletion 𝔫 C)) [𝔭.IsPrime] (h𝔭 : ¬ 𝔭.IsMaximal)
    (hs𝔭 : algebraMap O (AdicCompletion 𝔫 C) s ∈ 𝔭) :
    IsRegularLocalRing (Localization.AtPrime 𝔭) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_isRegularLocalRing_localization_atPrime_of_mem_of_not_isMaximal_of_tame.solution
