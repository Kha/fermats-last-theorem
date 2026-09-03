import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import P2M.Util
import P2M.Sol.S_IntermediateField_exists_le_isGalois_ringHom_dvd_finrank_of_ramificationIdx_eq_one
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand ExtCitation
open scoped Classical

theorem IntermediateField.exists_le_isGalois_ringHom_dvd_finrank_of_ramificationIdx_eq_one
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L' : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L'] (hL' : L'.IsUnramifiedOutside S)
    (F₀ : Type) [Field F₀] [NumberField F₀] [Algebra ↥L' F₀] [IsGalois ↥L' F₀]
    (hunr : ∀ w : HeightOneSpectrum (𝓞 F₀), w ∉ NumberField.placesOverPrimes F₀ (↑S : Set Nat.Primes) →
      Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ↥L')) w.asIdeal = 1) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L' ≤ F) (_ : NumberField ↥F) (_ : IsGalois ℚ ↥F) (e : F₀ →+* ↥F),
      (∀ x : ↥L', e (algebraMap ↥L' F₀ x) = IntermediateField.inclusion hLF x) ∧
      F.IsUnramifiedOutside S ∧ p ∣ Module.finrank ↥L' ↥(IntermediateField.extendScalars hLF) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_exists_le_isGalois_ringHom_dvd_finrank_of_ramificationIdx_eq_one.solution
