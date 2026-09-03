import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_HaarQuotient_map_mk_withDensity_eq_smul_measure

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem HaarQuotient.map_mk_withDensity_eq_smul_measure
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (c : ℝ≥0∞)
    (hρc : ∀ g : G, ∫⁻ x : H, ρ ((x : G) * g) ∂μH = c) :
    Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) (μ.withDensity ρ) =
      c • HaarQuotient.measure μ H μH := by p2m_exact_reverting @_root_.P2MW.S_HaarQuotient_map_mk_withDensity_eq_smul_measure.solution
