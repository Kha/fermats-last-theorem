import Mathlib
import P2M.Util
namespace P2MW.S_Algebra_Etale_of_isReduced_of_perfectField

set_option autoImplicit false
set_option maxHeartbeats 1600000

attribute [local instance] Ideal.Quotient.field in
theorem solution
    (K B : Type*) [Field K] [PerfectField K] [CommRing B] [Algebra K B]
    [Module.Finite K B] [IsReduced B] : Algebra.Etale K B := by
  haveI hArt : IsArtinianRing B := .of_finite K B
  have hfe : Algebra.FormallyEtale K B := by
    have hI (I : MaximalSpectrum B) : Algebra.FormallyEtale K (B ⧸ I.asIdeal) := by
      haveI : I.asIdeal.IsMaximal := I.isMaximal
      haveI : Module.Finite K (B ⧸ I.asIdeal) := Module.Finite.quotient K _
      haveI : Algebra.IsAlgebraic K (B ⧸ I.asIdeal) := Algebra.IsIntegral.isAlgebraic
      haveI : Algebra.IsSeparable K (B ⧸ I.asIdeal) := inferInstance
      exact Algebra.FormallyEtale.of_isSeparable K (B ⧸ I.asIdeal)
    exact Algebra.FormallyEtale.of_equiv ((IsArtinianRing.equivPi B).restrictScalars K).symm
  haveI : Algebra.FiniteType K B := inferInstance
  exact ⟨hfe, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
