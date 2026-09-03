import Mathlib
import Definitions.Def_AdicCompletionGaloisAction
import P2M.Util
import P2M.Sol.S_Algebra_isUnramifiedAt_adicCompletion_of_forall_not_isMaximal_of_not_mem
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp] AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul

set_option autoImplicit false

open IsLocalRing
open scoped AdicCompletion.GaloisAction

theorem Algebra.isUnramifiedAt_adicCompletion_of_forall_not_isMaximal_of_not_mem
    {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    {C : Type} [CommRing C] [Algebra O C] [Module.Finite O C]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)]
    (S : Type) [CommRing S] [IsLocalRing S] [Algebra C S] [IsLocalization.AtPrime S 𝔫]
    [Algebra O S] [IsScalarTower O C S]
    (s : O)
    (hunr : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], ¬ 𝔮.IsMaximal → algebraMap O S s ∉ 𝔮 → Algebra.IsUnramifiedAt O 𝔮)
    (𝔭 : Ideal (AdicCompletion 𝔫 C)) [𝔭.IsPrime] (h𝔭 : ¬ 𝔭.IsMaximal)
    (hs𝔭 : algebraMap O (AdicCompletion 𝔫 C) s ∉ 𝔭) :
    Algebra.IsUnramifiedAt (AdicCompletion (maximalIdeal O) O) 𝔭 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isUnramifiedAt_adicCompletion_of_forall_not_isMaximal_of_not_mem.solution
