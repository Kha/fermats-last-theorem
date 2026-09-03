import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_mem_smul_top_of_isLocalizedModule_primeCompl_of_isPrime_span_singleton

set_option autoImplicit false

open scoped Pointwise

theorem Submodule.mem_smul_top_of_isLocalizedModule_primeCompl_of_isPrime_span_singleton
    {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M] [Module.Projective A M]
    [AddCommGroup N] [Module A N]
    (ϖ : A) (hϖ : (Ideal.span {ϖ} : Ideal A).IsPrime)
    (𝔭 : Ideal A) [𝔭.IsPrime] (h𝔭 : ϖ ∈ 𝔭)
    (f : M →ₗ[A] N) [IsLocalizedModule 𝔭.primeCompl f]
    (m : M) (hm : f m ∈ ϖ • (⊤ : Submodule A N)) :
    m ∈ ϖ • (⊤ : Submodule A M) := by p2m_exact_reverting @_root_.P2MW.S_Submodule_mem_smul_top_of_isLocalizedModule_primeCompl_of_isPrime_span_singleton.solution
