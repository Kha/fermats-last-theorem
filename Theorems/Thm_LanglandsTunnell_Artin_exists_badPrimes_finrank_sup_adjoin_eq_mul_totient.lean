import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Artin_exists_badPrimes_finrank_sup_adjoin_eq_mul_totient

set_option autoImplicit false

universe u v

theorem LanglandsTunnell.Artin.exists_badPrimes_finrank_sup_adjoin_eq_mul_totient
    {K : Type u} [Field K] [NumberField K] {Ω : Type v} [Field Ω] [Algebra K Ω]
    (F : IntermediateField K Ω) [FiniteDimensional K F] :
    ∃ B₀ : Finset ℕ, (∀ p ∈ B₀, p.Prime) ∧
      ∀ (m : ℕ) [NeZero m] (ζ : Ω), IsPrimitiveRoot ζ m → (∀ p ∈ m.primeFactors, p ∉ B₀) →
        Module.finrank K ↥(F ⊔ IntermediateField.adjoin K {ζ}) = Module.finrank K F * m.totient := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Artin_exists_badPrimes_finrank_sup_adjoin_eq_mul_totient.solution
