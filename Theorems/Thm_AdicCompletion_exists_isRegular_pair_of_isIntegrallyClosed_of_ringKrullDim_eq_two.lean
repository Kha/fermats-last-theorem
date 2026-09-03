import Mathlib
import Definitions.Def_AdicCompletionGaloisAction
import P2M.Util
import P2M.Sol.S_AdicCompletion_exists_isRegular_pair_of_isIntegrallyClosed_of_ringKrullDim_eq_two
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open IsLocalRing
open scoped AdicCompletion.GaloisAction

theorem AdicCompletion.exists_isRegular_pair_of_isIntegrallyClosed_of_ringKrullDim_eq_two {O : Type} [CommRing O] [IsRegularLocalRing O] (hdimO : ringKrullDim O = 2)
    {C : Type} [CommRing C] [IsDomain C] (hCic : IsIntegrallyClosed C) [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)] :
    ∃ a b : AdicCompletion 𝔫 C, RingTheory.Sequence.IsRegular (AdicCompletion 𝔫 C) [a, b] := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_exists_isRegular_pair_of_isIntegrallyClosed_of_ringKrullDim_eq_two.solution
