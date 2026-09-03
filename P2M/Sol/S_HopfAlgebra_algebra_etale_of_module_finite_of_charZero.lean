import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.HopfAlgebra.Basic
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import P2M.Util
namespace P2MW.S_HopfAlgebra_algebra_etale_of_module_finite_of_charZero

set_option maxHeartbeats 3200000

attribute [local instance] Ideal.Quotient.field

theorem solution
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Module.Finite K A] :
    Algebra.Etale K A := by

  haveI : Algebra.FiniteType K A := inferInstance

  haveI : IsReduced A := HopfAlgebra.isReduced_of_finiteType_of_charZero K A

  haveI : IsArtinianRing A := .of_finite K A
  haveI : Finite (MaximalSpectrum A) := inferInstance

  have hI (I : MaximalSpectrum A) : Algebra.FormallyEtale K (A ⧸ I.asIdeal) := by
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    haveI : Module.Finite K (A ⧸ I.asIdeal) := Module.Finite.quotient K _
    haveI : Algebra.IsAlgebraic K (A ⧸ I.asIdeal) := Algebra.IsIntegral.isAlgebraic
    haveI : Algebra.IsSeparable K (A ⧸ I.asIdeal) := inferInstance
    exact Algebra.FormallyEtale.of_isSeparable K (A ⧸ I.asIdeal)
  refine ⟨?_, ?_⟩
  ·
    exact Algebra.FormallyEtale.of_equiv
      ((IsArtinianRing.equivPi A).restrictScalars K).symm
  ·
    exact Algebra.FinitePresentation.of_finiteType.mp inferInstance
