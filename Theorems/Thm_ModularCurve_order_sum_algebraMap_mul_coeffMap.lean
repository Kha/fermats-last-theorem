import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_order_sum_algebraMap_mul_coeffMap

open AlgebraicCurve ModularCurve
theorem ModularCurve.order_sum_algebraMap_mul_coeffMap {K K' : Type*} [Field K] [Field K'] (σ : K →+* K') {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (c : ι → K') (hc : ∀ a : ι → K, ∑ i ∈ s, σ (a i) * c i = 0 → ∀ i ∈ s, a i = 0)
    (f : ι → LaurentSeries K) (hf : ∀ i ∈ s, f i ≠ 0) :
    (∑ i ∈ s, algebraMap K' (LaurentSeries K') (c i) * coeffMap σ (f i)) ≠ 0 ∧
      (∑ i ∈ s, algebraMap K' (LaurentSeries K') (c i) * coeffMap σ (f i)).order
        = s.inf' hs (fun i => (f i).order) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_order_sum_algebraMap_mul_coeffMap.solution
