import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.Fixed
import Mathlib.Algebra.BigOperators.Pi
import P2M.Util
import P2M.Sol.S_M4aLocalCFT_decompositionSubgroup_exists_integralNormalBasis

set_option autoImplicit false

theorem M4aLocalCFT.decompositionSubgroup_exists_integralNormalBasis
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    [Finite (A.decompositionSubgroup K)] :
    letI := Fintype.ofFinite (A.decompositionSubgroup K)
    ∃ α : L, α ∈ A ∧
      LinearIndependent (FixedPoints.subfield (A.decompositionSubgroup K) L)
        (fun s : A.decompositionSubgroup K => s • α) ∧
      ∃ d : L, d ∈ A ∧ d ≠ 0 ∧ (∀ s : A.decompositionSubgroup K, s • d = d) ∧
        ∀ a : L, a ∈ A → ∃ c : A.decompositionSubgroup K → L,
          (∀ s, c s ∈ A) ∧ (∀ s t : A.decompositionSubgroup K, t • c s = c s) ∧
          d * a = ∑ s, c s * s • α := by p2m_exact_reverting @_root_.P2MW.S_M4aLocalCFT_decompositionSubgroup_exists_integralNormalBasis.solution
