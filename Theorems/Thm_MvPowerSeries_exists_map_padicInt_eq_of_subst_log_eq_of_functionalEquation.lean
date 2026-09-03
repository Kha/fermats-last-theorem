import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_map_padicInt_eq_of_subst_log_eq_of_functionalEquation

set_option autoImplicit false

universe u

theorem MvPowerSeries.exists_map_padicInt_eq_of_subst_log_eq_of_functionalEquation
    (p : ℕ) [Fact p.Prime] (d : ℕ) {τ : Type u}
    (a : ℕ → Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (f : Fin d → MvPowerSeries (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (h1 : a 0 = 1)
    (h2 : ∀ k : ℕ, (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (k + 1)
      = ∑ m ∈ Finset.range (k + 1),
          (Matrix.of fun i j => MvPolynomial.X (m, i, j)) *
            (a (k - m)).map (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p))^[m + 1])
    (h3 : ∀ (i j : Fin d) (k : ℕ), ((f i).coeff (Finsupp.single j (p ^ k)) : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = a k i j)
    (h4 : ∀ (i : Fin d) (e : Fin d →₀ ℕ),
      (∀ (j : Fin d) (k : ℕ), e ≠ Finsupp.single j (p ^ k)) → ((f i).coeff e : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = 0)
    (Θ : Fin d → MvPowerSeries τ (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (hΘ : ∀ i, (Θ i).constantCoeff = 0)
    (g : Fin d → MvPowerSeries τ (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (hfg : ∀ i, MvPowerSeries.subst Θ (f i) = g i)
    (hFE : ∀ (i : Fin d) (e : τ →₀ ℕ), ∃ r : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p),
      (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) * (g i).coeff e
        - ∑ m ∈ Finset.range (Finsupp.degree e), ∑ l : Fin d,
            MvPolynomial.X (m, i, l) *
              (MvPowerSeries.expand (p ^ (m + 1)) (pow_ne_zero (m + 1) (Fact.out : p.Prime).ne_zero)
                (MvPowerSeries.map
                  ((MvPolynomial.aeval fun v => MvPolynomial.X v ^ p :
                      MvPolynomial (ℕ × Fin d × Fin d) (Padic p) →ₐ[Padic p]
                        MvPolynomial (ℕ × Fin d × Fin d) (Padic p)).toRingHom ^ (m + 1)) (g l))).coeff e
        = (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p))
            * MvPolynomial.map (PadicInt.Coe.ringHom (p := p)) r) :
    ∃ Θ₀ : Fin d → MvPowerSeries τ (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)),
      ∀ i, MvPowerSeries.map (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) (Θ₀ i) = Θ i := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_map_padicInt_eq_of_subst_log_eq_of_functionalEquation.solution
