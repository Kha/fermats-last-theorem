import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_comp_mul_eq_one

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_continuous_hasCompactSupport_forall_integral_comp_mul_eq_one
    {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (τ : Measure H) [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    (ι : H →* G) (hι : Topology.IsClosedEmbedding ι)
    (K : Set G) (hK : IsCompact K) :
    ∃ w : G → ℝ, Continuous w ∧ HasCompactSupport w ∧ (∀ g, 0 ≤ w g) ∧
      ∀ (h : H) (k : G), k ∈ K → ∫ h', w (ι h' * (ι h * k)) ∂τ = 1 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_comp_mul_eq_one.solution
