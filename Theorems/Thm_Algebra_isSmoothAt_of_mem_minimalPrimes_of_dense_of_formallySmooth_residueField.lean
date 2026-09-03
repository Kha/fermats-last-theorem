import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField

set_option autoImplicit false

universe u

theorem Algebra.isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField
    {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [IsReduced B]
    (S : Set (PrimeSpectrum B))
    (hdense : ∀ g : B, (∀ 𝔰 ∈ S, g ∈ 𝔰.asIdeal) → g = 0)
    (hsep : ∀ 𝔰 ∈ S, ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      Algebra.FormallySmooth k K ∧ Nonempty (𝔰.asIdeal.ResidueField →ₐ[k] K))
    (𝔮 : Ideal B) [𝔮.IsPrime] (h𝔮 : 𝔮 ∈ minimalPrimes B) :
    Algebra.IsSmoothAt k 𝔮 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField.solution
