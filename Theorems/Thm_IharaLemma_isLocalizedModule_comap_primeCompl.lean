import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Ideal.Maps
import P2M.Util
import P2M.Sol.S_IharaLemma_isLocalizedModule_comap_primeCompl

set_option autoImplicit false

theorem IharaLemma.isLocalizedModule_comap_primeCompl {Λ B : Type*} [CommRing Λ] [CommRing B] [Algebra Λ B]
    (hπ : Function.Surjective (algebraMap Λ B))
    (𝔭 : Ideal B) [𝔭.IsPrime]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N] [Module Λ M] [Module Λ N]
    [IsScalarTower Λ B M] [IsScalarTower Λ B N]
    (f : M →ₗ[B] N) [IsLocalizedModule 𝔭.primeCompl f] :
    IsLocalizedModule (𝔭.comap (algebraMap Λ B)).primeCompl (f.restrictScalars Λ) := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_isLocalizedModule_comap_primeCompl.solution
