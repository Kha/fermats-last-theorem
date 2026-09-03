import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_HaarQuotient_measurable_lintegral_mul_out

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem HaarQuotient.measurable_lintegral_mul_out
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => ∫⁻ x, f ((x : G) * q.out) ∂μH := by p2m_exact_reverting @_root_.P2MW.S_HaarQuotient_measurable_lintegral_mul_out.solution
