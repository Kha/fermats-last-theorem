import Definitions.Def_HaarQuotient
import Mathlib.MeasureTheory.Measure.Haar.Basic
import P2M.Util
import P2M.Sol.S_HaarQuotient_withDensity_density_coe_mul_lt_top_of_isCompact

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Pointwise

theorem HaarQuotient.withDensity_density_coe_mul_lt_top_of_isCompact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (hK₀ : ∃ K₀ : Subgroup G, IsOpen (K₀ : Set G) ∧ IsCompact (K₀ : Set G))
    (K : Set G) (hK : IsCompact K) :
    (μ.withDensity (HaarQuotient.density H μH)) ((H : Set G) * K) < ⊤ := by p2m_exact_reverting @_root_.P2MW.S_HaarQuotient_withDensity_density_coe_mul_lt_top_of_isCompact.solution
