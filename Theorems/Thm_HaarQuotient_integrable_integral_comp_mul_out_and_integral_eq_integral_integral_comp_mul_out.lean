import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_HaarQuotient_integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem HaarQuotient.integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ℂ) (hf : Measurable f) (hfi : ∫⁻ g, ‖f g‖ₑ ∂μ < ∞) :
    (∀ᵐ q ∂(HaarQuotient.measure μ H μH), Integrable (fun x : H => f ((x : G) * q.out)) μH) ∧
    Integrable (fun q : MulAction.orbitRel.Quotient H G => (∫ x : H, f ((x : G) * q.out) ∂μH))
      (HaarQuotient.measure μ H μH) ∧
    ∫ g, f g ∂μ = ∫ q, (∫ x : H, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH) := by p2m_exact_reverting @_root_.P2MW.S_HaarQuotient_integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out.solution
