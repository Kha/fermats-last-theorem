import Mathlib
import Definitions.Def_AdicCompletionGaloisAction
import P2M.Util
import P2M.Sol.S_AdicCompletion_isLocalRing_and_ringKrullDim_le_two_of_liesOver
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open IsLocalRing
open scoped AdicCompletion.GaloisAction

theorem AdicCompletion.isLocalRing_and_ringKrullDim_le_two_of_liesOver {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] (hdimO : ringKrullDim O = 2)
    {C : Type} [CommRing C] [Algebra O C] [Module.Finite O C]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)] :
    IsLocalRing (AdicCompletion 𝔫 C) ∧ ringKrullDim (AdicCompletion 𝔫 C) ≤ (2 : WithBot ℕ∞) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_isLocalRing_and_ringKrullDim_le_two_of_liesOver.solution
