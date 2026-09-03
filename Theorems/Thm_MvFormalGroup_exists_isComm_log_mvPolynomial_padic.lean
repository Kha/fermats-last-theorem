import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import P2M.Util
import P2M.Sol.S_MvFormalGroup_exists_isComm_log_mvPolynomial_padic

set_option autoImplicit false

universe u

theorem MvFormalGroup.exists_isComm_log_mvPolynomial_padic
    (p : ℕ) [Fact p.Prime] (d : ℕ) :
    ∃ (Φ : MvFormalGroup d (MvPolynomial (ℕ × Fin d × Fin d) (Padic p))) (_ : Φ.IsComm)
      (a : ℕ → Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
      (f : Fin d → MvPowerSeries (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p))),
      a 0 = 1 ∧
      (∀ k : ℕ, (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (k + 1)
        = ∑ m ∈ Finset.range (k + 1),
            (Matrix.of fun i j => MvPolynomial.X (m, i, j)) *
              (a (k - m)).map (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p))^[m + 1]) ∧
      (∀ (i j : Fin d) (k : ℕ), ((f i).coeff (Finsupp.single j (p ^ k)) : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = a k i j) ∧
      (∀ (i : Fin d) (e : Fin d →₀ ℕ),
        (∀ (j : Fin d) (k : ℕ), e ≠ Finsupp.single j (p ^ k)) → ((f i).coeff e : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = 0) ∧
      (∀ i : Fin d,
        MvPowerSeries.subst Φ.toPowerSeries (f i)
          = MvPowerSeries.subst (fun j => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))) (f i)
            + MvPowerSeries.subst (fun j => MvPowerSeries.X (Sum.inr j)) (f i)) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_exists_isComm_log_mvPolynomial_padic.solution
