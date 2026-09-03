import Mathlib
import Theorems.Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_mem_range_of_isPrime_span_of_forall_height_eq_one_of_notMem

set_option autoImplicit false

theorem IsIntegrallyClosed.mem_range_of_isPrime_span_of_forall_height_eq_one_of_notMem
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    {F : Type*} [Field F] (ι : B →+* F) (hι : Function.Injective ι)
    (ϖ : B) (hϖ : ϖ ≠ 0) (hprime : (Ideal.span {ϖ}).IsPrime)
    (x : F)
    (hV : ∃ a s : B, s ∉ Ideal.span {ϖ} ∧ x * ι s = ι a)
    (hH : ∀ P : Ideal B, P.IsPrime → P.height = 1 → ϖ ∉ P → ∃ a s : B, s ∉ P ∧ x * ι s = ι a) :
    x ∈ ι.range := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_mem_range_of_isPrime_span_of_forall_height_eq_one_of_notMem.solution
