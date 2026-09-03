import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_HaarQuotient_lintegral_comp_out_mul_eq_of_map_mul_right_eq

open MeasureTheory

theorem HaarQuotient.lintegral_comp_out_mul_eq_of_map_mul_right_eq
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ENNReal) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) (k : G)
    (hμk : Measure.map (· * k) μ = μ) :
    ∫⁻ q : MulAction.orbitRel.Quotient H G, f (q.out * k) ∂(HaarQuotient.measure μ H μH) =
      ∫⁻ q : MulAction.orbitRel.Quotient H G, f q.out ∂(HaarQuotient.measure μ H μH) := by p2m_exact_reverting @_root_.P2MW.S_HaarQuotient_lintegral_comp_out_mul_eq_of_map_mul_right_eq.solution
