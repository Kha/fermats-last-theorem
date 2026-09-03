import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_exists_lintegral_mul_density_archMeasure_le_lintegral_iwasawa

set_option autoImplicit false

open MeasureTheory AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates RSCarrier

theorem LanglandsTunnell.Converse.exists_lintegral_mul_density_archMeasure_le_lintegral_iwasawa :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (μN : Measure realUnipotent) [μN.IsHaarMeasure]
      (ν : Measure (rowIsometrySubgroup ℝ)) [ν.IsHaarMeasure],
    ∃ C₀ : ENNReal, C₀ ≠ ⊤ ∧
      ∀ (H : GL (Fin 2) ℝ → ENNReal), Measurable H →
        (∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, H (n * g) = H g) →
        MeasureTheory.lintegral RSCarrier.archMeasure (fun g => H g * HaarQuotient.density realUnipotent μN g) ≤
          C₀ * MeasureTheory.lintegral ν (fun k : rowIsometrySubgroup ℝ =>
            MeasureTheory.lintegral (volume : Measure (ℝ × ℝ)) (fun q : ℝ × ℝ =>
              if h : 0 < q.1 ∧ 0 < q.2 then
                H (upperUnit (q.2 * q.1) 0 q.2 (mul_pos h.2 h.1).ne' h.2.ne' * (k : GL (Fin 2) ℝ)) *
                  ENNReal.ofReal ((q.1 ^ 2)⁻¹ * q.2⁻¹)
              else 0)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_exists_lintegral_mul_density_archMeasure_le_lintegral_iwasawa.solution
