import Definitions.Def_HaarQuotient
import P2M.Util
import P2M.Sol.S_HaarQuotient_setLIntegral_withDensity_eq_inv_mul_setLIntegral_of_forall_lintegral_eq

open MeasureTheory

theorem HaarQuotient.setLIntegral_withDensity_eq_inv_mul_setLIntegral_of_forall_lintegral_eq
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (H : Subgroup G) (μH : Measure ↥H) [μH.IsMulRightInvariant]
    (ρ : G → ENNReal)
    (hquot : ∀ h : G → ENNReal, Measurable h →
      ∫⁻ g, h g ∂μ = ∫⁻ q, (∫⁻ x, h ((x : G) * q.out) ∂μH)
        ∂(Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) (μ.withDensity ρ)))
    (K : Subgroup G) (hK : IsClosed (K : Set G)) (t : G) (S : Set G) (hS : MeasurableSet S)
    (hmemS : ∀ g : G, g ∈ S ↔ ∃ x ∈ H, ∃ k ∈ K, g = x * t * k)
    (D : ENNReal) (hD : μH {y : ↥H | t⁻¹ * (y : G) * t ∈ K} = D) (hD0 : D ≠ 0) (hDtop : D ≠ ⊤)
    (f : G → ENNReal) (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) :
    ∫⁻ g in S, f g ∂(μ.withDensity ρ) = D⁻¹ * ∫⁻ k in (K : Set G), f (t * k) ∂μ := by p2m_exact_reverting @_root_.P2MW.S_HaarQuotient_setLIntegral_withDensity_eq_inv_mul_setLIntegral_of_forall_lintegral_eq.solution
