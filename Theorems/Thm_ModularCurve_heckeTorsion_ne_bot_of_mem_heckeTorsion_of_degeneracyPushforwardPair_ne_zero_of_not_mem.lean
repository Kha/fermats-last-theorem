import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeTorsion_ne_bot_of_mem_heckeTorsion_of_degeneracyPushforwardPair_ne_zero_of_not_mem
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.heckeTorsion_ne_bot_of_mem_heckeTorsion_of_degeneracyPushforwardPair_ne_zero_of_not_mem
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (hin : HeckeInputsAll (N₀ * p)) (hcomm : HeckeOperatorsCommuteBar (N₀ * p))
    (hinN : HeckeInputsAll N₀) (hcommN : HeckeOperatorsCommuteBar N₀)
    (𝔪 : Ideal HeckeAlg) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪) (hU : heckeGen ⟨p, Fact.out⟩ ∉ 𝔪)
    (x : JZero (N₀ * p))
    (hx𝔪 : letI := heckeModuleBar (N₀ * p); x ∈ heckeTorsion (JZero (N₀ * p)) 𝔪)
    (hx : degeneracyPushforwardPair N₀ p 0 x ≠ 0 ∨ degeneracyPushforwardPair N₀ p 1 x ≠ 0) :
    letI := heckeModuleBar N₀
    heckeTorsion (JZero N₀) 𝔪 ≠ ⊥ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeTorsion_ne_bot_of_mem_heckeTorsion_of_degeneracyPushforwardPair_ne_zero_of_not_mem.solution
