import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_exists_valuationSubring_admissibleConstants_over_cyclotomic

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups Classical

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_valuationSubring_admissibleConstants_over_cyclotomic
    (q : ℕ) [Fact q.Prime] (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) :
    ∃ (Abar : ValuationSubring (AlgebraicClosure ℚ)) (_ : Abar.LiesOverPrime q)
      (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (ι : L →+* ↥k₀) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ Abar),

      IsDiscreteValuationRing ↥(Abar.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ∧
      maximalIdeal ↥(Abar.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) = Ideal.span {(⟨π₀, hπ⟩ : ↥(Abar.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))} ∧
      HenselianLocalRing ↥(Abar.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ∧
      IsAlgClosed (ResidueField ↥(Abar.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧
      (∀ a : (AlgebraicClosure ℚ), a ∈ Abar → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ Abar ∧ ∃ h : a - c ∈ Abar, (⟨_, h⟩ : Abar) ∈ maximalIdeal Abar) ∧

      (∀ a : A, ((ι (algebraMap A L a) : ↥k₀) : (AlgebraicClosure ℚ)) ∈ Abar) ∧
      (∀ x : L, ((ι x : ↥k₀) : (AlgebraicClosure ℚ)) ∈ Abar → ∃ a : A, algebraMap A L a = x) ∧

      (∃ ιC : ↥k₀ →+* ℂ, ιC (ι ξ) = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_exists_valuationSubring_admissibleConstants_over_cyclotomic.solution
