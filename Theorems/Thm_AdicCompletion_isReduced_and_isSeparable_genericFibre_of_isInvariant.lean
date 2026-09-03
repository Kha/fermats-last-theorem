import Mathlib
import Definitions.Def_AdicCompletionGaloisAction
import P2M.Util
import P2M.Sol.S_AdicCompletion_isReduced_and_isSeparable_genericFibre_of_isInvariant
attribute [-simp] AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul

set_option autoImplicit false

open IsLocalRing
open scoped AdicCompletion.GaloisAction

theorem AdicCompletion.isReduced_and_isSeparable_genericFibre_of_isInvariant {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    {C : Type} [CommRing C] [IsDomain C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    {G : Type} [Group G] [Finite G] [MulSemiringAction G C] [SMulCommClass G O C] [FaithfulSMul G C]
    [Algebra.IsInvariant O C G]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)]
    (K₀ : Type) [Field K₀] [Algebra (AdicCompletion (maximalIdeal O) O) K₀] [IsFractionRing (AdicCompletion (maximalIdeal O) O) K₀]
    (F : Type) [CommRing F] [Algebra (AdicCompletion 𝔫 C) F] [Algebra (AdicCompletion (maximalIdeal O) O) F] [Algebra K₀ F]
    [IsScalarTower (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) F]
    [IsScalarTower (AdicCompletion (maximalIdeal O) O) K₀ F]
    [IsLocalization (Algebra.algebraMapSubmonoid (AdicCompletion 𝔫 C) (nonZeroDivisors (AdicCompletion (maximalIdeal O) O))) F] :
    IsReduced F ∧ Algebra.IsSeparable K₀ F := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_isReduced_and_isSeparable_genericFibre_of_isInvariant.solution
