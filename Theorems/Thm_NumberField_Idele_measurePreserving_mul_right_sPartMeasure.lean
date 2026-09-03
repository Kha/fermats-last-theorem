import Definitions.Def_NumberField_IdeleProductMeasure
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import P2M.Util
import P2M.Sol.S_NumberField_Idele_measurePreserving_mul_right_sPartMeasure

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal Classical

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem NumberField.Idele.measurePreserving_mul_right_sPartMeasure
    (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (u : (AdeleRing (𝓞 K) K)ˣ) (_huS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((u : AdeleRing (𝓞 K) K)).2 v = 1) :
    MeasurePreserving (fun t : (AdeleRing (𝓞 K) K)ˣ => t * u) (NumberField.Idele.sPartMeasure K S) (NumberField.Idele.sPartMeasure K S) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Idele_measurePreserving_mul_right_sPartMeasure.solution
