import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_crossingPresentation_of_ringEquiv_adicCompletion_uvCrossingModel
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal
set_option autoImplicit false

open ModularCurve

theorem IsLocalRing.exists_crossingPresentation_of_ringEquiv_adicCompletion_uvCrossingModel
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+* UVCrossingModel W (π ^ E))
    (ϖ g h : R)
    (hϖ : ι (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) ϖ) = UVCrossingModel.const (π ^ E) π)
    (hg : Ideal.map ι (Ideal.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) (Ideal.span {ϖ, g}))
      = Ideal.span {UVCrossingModel.const (π ^ E) π, UVCrossingModel.U (π ^ E)})
    (hh : Ideal.map ι (Ideal.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) (Ideal.span {ϖ, h}))
      = Ideal.span {UVCrossingModel.const (π ^ E) π, UVCrossingModel.V (π ^ E)}) :
    ∃ g' h' w : R, IsUnit w ∧ g' * h' = ϖ ^ E * w ∧
      IsLocalRing.maximalIdeal R = Ideal.span {ϖ, g', h'} ∧
      (Ideal.span {ϖ, g'}).IsPrime ∧ (Ideal.span {ϖ, h'}).IsPrime ∧
      h' ∉ Ideal.span {ϖ, g'} ∧ g' ∉ Ideal.span {ϖ, h'} ∧
      Ideal.span {ϖ, g'} = Ideal.span {ϖ, g} ∧ Ideal.span {ϖ, h'} = Ideal.span {ϖ, h} := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_crossingPresentation_of_ringEquiv_adicCompletion_uvCrossingModel.solution
