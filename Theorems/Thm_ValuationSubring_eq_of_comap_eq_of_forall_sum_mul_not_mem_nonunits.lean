import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_eq_of_comap_eq_of_forall_sum_mul_not_mem_nonunits

set_option autoImplicit false

open scoped BigOperators

theorem ValuationSubring.eq_of_comap_eq_of_forall_sum_mul_not_mem_nonunits
    {K K' : Type*} [Field K] [Field K'] (ι : K →+* K') (n : ℕ)
    (b : Fin n → K') (hb : ∀ z : K', ∃ c : Fin n → K, z = ∑ i, ι (c i) * b i)
    (W : ValuationSubring K) (U : ValuationSubring K') (hU : U.comap ι = W)
    (u : Fin n → K') (hu : ∀ i, u i ∈ U)
    (hind : ∀ c : Fin n → K, (∀ i, c i ∈ W) → (∃ i, c i ∉ W.nonunits) → ∑ i, ι (c i) * u i ∉ U.nonunits)
    (V : ValuationSubring K') (hV : V.comap ι = W) :
    V = U := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_eq_of_comap_eq_of_forall_sum_mul_not_mem_nonunits.solution
