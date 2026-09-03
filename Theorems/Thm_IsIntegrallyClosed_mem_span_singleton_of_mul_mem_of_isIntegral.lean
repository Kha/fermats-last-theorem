import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_mem_span_singleton_of_mul_mem_of_isIntegral

universe u

theorem IsIntegrallyClosed.mem_span_singleton_of_mul_mem_of_isIntegral
    {R A : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra R A] [FaithfulSMul R A] [Algebra.IsIntegral R A]
    {p : R} (hp : (Ideal.span {p}).IsPrime) (hp0 : p ≠ 0)
    {s : R} (hs : s ∉ Ideal.span {p}) {a : A}
    (h : algebraMap R A s * a ∈ Ideal.span {algebraMap R A p}) :
    a ∈ Ideal.span {algebraMap R A p} := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_mem_span_singleton_of_mul_mem_of_isIntegral.solution
