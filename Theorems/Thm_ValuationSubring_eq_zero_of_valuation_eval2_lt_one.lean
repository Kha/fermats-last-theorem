import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_eq_zero_of_valuation_eval2_lt_one

set_option autoImplicit false

universe u v

theorem ValuationSubring.eq_zero_of_valuation_eval2_lt_one
    {k : Type u} {K : Type v} [Field k] [Field K] (c : k →+* K) (O : ValuationSubring K)
    (hc : ∀ x : k, c x ∈ O) {d : ℕ} (g : Fin d → K) (hg : ∀ i, g i ∈ O)
    (hind :
      letI : Algebra k (IsLocalRing.ResidueField O) :=
        ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra
      AlgebraicIndependent k (fun i => IsLocalRing.residue O ⟨g i, hg i⟩))
    (Q : MvPolynomial (Fin d) k) (hQ : O.valuation (Q.eval₂ c g) < 1) : Q = 0 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_eq_zero_of_valuation_eval2_lt_one.solution
