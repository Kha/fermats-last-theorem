import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_gram_denominator_of_mulTable

set_option autoImplicit false
theorem AlgebraicCurve.Place.exists_gram_denominator_of_mulTable
    {K₀ k F : Type*} [Field K₀] [Field k] [Field F] [Algebra K₀ k] [Algebra k F]
    {j : F} (hj : Transcendental k j)
    [FiniteDimensional (IntermediateField.adjoin k ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({j} : Set F)) F]
    (n : ℕ) (b : Fin n → F)
    (hbli : ∀ c : Fin n → Polynomial k,
      (∑ i : Fin n, Polynomial.aeval j (c i) * b i) = 0 → ∀ i, c i = 0)
    (hbsp : ∀ x : F, ∃ (q : Polynomial k) (c : Fin n → Polynomial k), q ≠ 0 ∧
      x * Polynomial.aeval j q = ∑ i : Fin n, Polynomial.aeval j (c i) * b i)
    (d : Polynomial K₀) (hd : d ≠ 0) (A : Fin n → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (hmul : ∀ i i' : Fin n, b i * b i' * Polynomial.aeval j (d.map (algebraMap K₀ k))
      = ∑ i'' : Fin n, Polynomial.aeval j ((A i i'' i').map (algebraMap K₀ k)) * b i'') :
    ∃ Δ : Polynomial K₀, Δ ≠ 0 ∧ ∀ x : F, IsIntegral (Algebra.adjoin k ({j} : Set F)) x →
      ∃ c : Fin n → Polynomial k,
        Polynomial.aeval j (Δ.map (algebraMap K₀ k)) * x
          = ∑ i : Fin n, Polynomial.aeval j (c i)
              * (Polynomial.aeval j (d.map (algebraMap K₀ k)) * b i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_gram_denominator_of_mulTable.solution
