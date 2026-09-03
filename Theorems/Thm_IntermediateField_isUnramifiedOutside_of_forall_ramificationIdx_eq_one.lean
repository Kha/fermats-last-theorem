import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import P2M.Util
import P2M.Sol.S_IntermediateField_isUnramifiedOutside_of_forall_ramificationIdx_eq_one

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand ExtCitation
open scoped Classical

theorem IntermediateField.isUnramifiedOutside_of_forall_ramificationIdx_eq_one
    (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] (hL : L.IsUnramifiedOutside S)
    [IsGalois ↥L ↥(IntermediateField.extendScalars hLF)]
    (h : ∀ w : HeightOneSpectrum (𝓞 ↥F), w ∉ NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes) →
      letI := (IntermediateField.inclusion hLF).toRingHom.toAlgebra
      Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ↥L)) w.asIdeal = 1) :
    F.IsUnramifiedOutside S := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_isUnramifiedOutside_of_forall_ramificationIdx_eq_one.solution
