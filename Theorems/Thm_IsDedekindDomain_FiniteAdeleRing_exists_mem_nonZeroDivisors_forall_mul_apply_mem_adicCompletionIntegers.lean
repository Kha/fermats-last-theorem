import Mathlib
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_FiniteAdeleRing_exists_mem_nonZeroDivisors_forall_mul_apply_mem_adicCompletionIntegers

open IsDedekindDomain

theorem IsDedekindDomain.FiniteAdeleRing.exists_mem_nonZeroDivisors_forall_mul_apply_mem_adicCompletionIntegers
    {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (a : IsDedekindDomain.FiniteAdeleRing A K) :
    ∃ d ∈ nonZeroDivisors A, ∀ v : IsDedekindDomain.HeightOneSpectrum A,
      algebraMap K (v.adicCompletion K) (algebraMap A K d) * a v ∈ v.adicCompletionIntegers K := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_mem_nonZeroDivisors_forall_mul_apply_mem_adicCompletionIntegers.solution
