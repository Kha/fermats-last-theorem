import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_memLp_two

set_option autoImplicit false

open MeasureTheory Topology
open scoped ENNReal

theorem MeasureTheory.exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_memLp_two
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (F : G → ℂ) (hF : MemLp F 2 μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ 𝓝 (1 : G), ∀ x ∈ V, eLpNorm (fun g => F (g * x) - F g) 2 μ < ENNReal.ofReal ε := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_memLp_two.solution
