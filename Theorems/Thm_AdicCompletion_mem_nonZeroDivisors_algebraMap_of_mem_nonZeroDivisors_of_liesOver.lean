import Mathlib
import Definitions.Def_AdicCompletionGaloisAction
import P2M.Util
import P2M.Sol.S_AdicCompletion_mem_nonZeroDivisors_algebraMap_of_mem_nonZeroDivisors_of_liesOver
attribute [-simp] AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul

set_option autoImplicit false

open IsLocalRing
open scoped AdicCompletion.GaloisAction

theorem AdicCompletion.mem_nonZeroDivisors_algebraMap_of_mem_nonZeroDivisors_of_liesOver {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    {C : Type} [CommRing C] [IsDomain C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)] :
    ∀ r : AdicCompletion (maximalIdeal O) O, r ∈ nonZeroDivisors (AdicCompletion (maximalIdeal O) O) →
      algebraMap (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) r ∈ nonZeroDivisors (AdicCompletion 𝔫 C) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_mem_nonZeroDivisors_algebraMap_of_mem_nonZeroDivisors_of_liesOver.solution
