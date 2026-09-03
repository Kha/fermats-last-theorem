import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_AdeleTopologyFacts
import P2M.Util
import P2M.Sol.S_NumberField_Idele_exists_forall_measure_eq_mul_idelicHaar

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ENNReal

theorem NumberField.Idele.exists_forall_measure_eq_mul_idelicHaar (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsHaarMeasure] :
    ∃ d : ℝ≥0∞, d ≠ 0 ∧ d ≠ ⊤ ∧ ∀ s : Set (AdeleRing (𝓞 K) K)ˣ, ν s = d * NumberField.Idele.idelicHaar K s := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Idele_exists_forall_measure_eq_mul_idelicHaar.solution
