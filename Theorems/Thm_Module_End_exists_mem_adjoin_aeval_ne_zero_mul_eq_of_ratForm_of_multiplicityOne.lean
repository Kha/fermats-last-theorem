import Mathlib
import P2M.Util
import P2M.Sol.S_Module_End_exists_mem_adjoin_aeval_ne_zero_mul_eq_of_ratForm_of_multiplicityOne

set_option autoImplicit false

theorem Module.End.exists_mem_adjoin_aeval_ne_zero_mul_eq_of_ratForm_of_multiplicityOne
    {L V σ : Type} [Field L] [CharZero L] [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    [Module ℚ V] [IsScalarTower ℚ L V]
    (VQ : Submodule ℚ V)
    (hli : ∀ (n : ℕ) (v : Fin n → V), (∀ i, v i ∈ VQ) →
      LinearIndependent ℚ v → LinearIndependent L v)
    (hspan : Submodule.span L (VQ : Set V) = ⊤)
    (ρ : MvPolynomial σ ℤ →+* Module.End L V)
    (hrat : ∀ (i : σ) (v : V), v ∈ VQ → ρ (MvPolynomial.X i) v ∈ VQ)
    (G : Set σ)
    (hss : ∀ i ∈ G, ∃ P : Polynomial ℚ, P.Separable ∧
      Polynomial.aeval (ρ (MvPolynomial.X i)) (P.map (algebraMap ℚ L)) = 0)
    (lam : σ → L) (v₀ : V) (hv₀ : v₀ ≠ 0)
    (heig : ∀ i ∈ G, ρ (MvPolynomial.X i) v₀ = lam i • v₀)
    (hmult : ∀ w : V, (∀ i ∈ G, ρ (MvPolynomial.X i) w = lam i • w) → ∃ c : L, w = c • v₀)
    (t : MvPolynomial σ ℤ) :
    ∃ s ∈ Algebra.adjoin ℤ (MvPolynomial.X '' G : Set (MvPolynomial σ ℤ)),
      ∃ u ∈ Algebra.adjoin ℤ (MvPolynomial.X '' G : Set (MvPolynomial σ ℤ)),
        MvPolynomial.aeval lam s ≠ 0 ∧ ρ s * ρ t = ρ u := by p2m_exact_reverting @_root_.P2MW.S_Module_End_exists_mem_adjoin_aeval_ne_zero_mul_eq_of_ratForm_of_multiplicityOne.solution
