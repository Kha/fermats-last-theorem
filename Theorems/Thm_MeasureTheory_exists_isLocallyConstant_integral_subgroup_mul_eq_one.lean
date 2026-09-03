import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_isLocallyConstant_integral_subgroup_mul_eq_one

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_isLocallyConstant_integral_subgroup_mul_eq_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K₀ : Subgroup G) (hK₀ : IsCompact (K₀ : Set G)) (hK₀' : IsOpen (K₀ : Set G))
    (T : Subgroup G) (hT : IsClosed (T : Set G)) (hcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    [MeasurableSpace T] [BorelSpace T] (τ : Measure T) [τ.IsHaarMeasure]
    (Ω : Set G) (hΩ : IsCompact Ω) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ IsLocallyConstant w ∧ HasCompactSupport w ∧
      ∀ x : G, (∃ t ∈ T, ∃ d ∈ Ω, x = t * d) → ∫ t : T, w (t * x) ∂τ = 1 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_isLocallyConstant_integral_subgroup_mul_eq_one.solution
