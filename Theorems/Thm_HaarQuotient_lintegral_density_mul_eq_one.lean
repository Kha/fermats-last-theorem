import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_HaarQuotient_lintegral_density_mul_eq_one

set_option autoImplicit false

open MeasureTheory

theorem HaarQuotient.lintegral_density_mul_eq_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (g : G) :
    ∫⁻ x : H, HaarQuotient.density H μH ((x : G) * g) ∂μH = 1 := by p2m_exact_reverting @_root_.P2MW.S_HaarQuotient_lintegral_density_mul_eq_one.solution
