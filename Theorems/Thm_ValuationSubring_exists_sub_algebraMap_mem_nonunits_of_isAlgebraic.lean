import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_sub_algebraMap_mem_nonunits_of_isAlgebraic

set_option autoImplicit false

universe u v w in

theorem ValuationSubring.exists_sub_algebraMap_mem_nonunits_of_isAlgebraic
    {K : Type u} [Field K] [IsAlgClosed K] {Ω : Type v} [Field Ω] [Algebra K Ω]
    {Ω' : Type w} [Field Ω'] [Algebra Ω Ω'] [Algebra K Ω'] [IsScalarTower K Ω Ω']
    [Algebra.IsAlgebraic Ω Ω']
    (A : ValuationSubring Ω) (hK : ∀ c : K, algebraMap K Ω c ∈ A)
    (hres : ∀ a : Ω, a ∈ A → ∃ c : K, a - algebraMap K Ω c ∈ A.nonunits)
    (O : ValuationSubring Ω') (hO : ∀ a : Ω, algebraMap Ω Ω' a ∈ O ↔ a ∈ A)
    (z : Ω') (hz : z ∈ O) : ∃ c : K, z - algebraMap K Ω' c ∈ O.nonunits := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_sub_algebraMap_mem_nonunits_of_isAlgebraic.solution
