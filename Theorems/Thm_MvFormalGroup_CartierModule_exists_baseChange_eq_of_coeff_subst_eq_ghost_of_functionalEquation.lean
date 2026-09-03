import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_exists_baseChange_eq_of_coeff_subst_eq_ghost_of_functionalEquation

set_option autoImplicit false

universe u
open MvPowerSeries in

theorem MvFormalGroup.CartierModule.exists_baseChange_eq_of_coeff_subst_eq_ghost_of_functionalEquation
    (p : ℕ) [Fact p.Prime] (d : ℕ)
    (Φ₀ : MvFormalGroup d (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p))) [Φ₀.IsComm]
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
    (c : ℕ → Fin d → MvPolynomial (ℕ × Fin d × Fin d) (Padic p))
    (hcA : ∀ (N : ℕ) (j : Fin d), ∃ r : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p),
      (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ N * c N j = MvPolynomial.map (PadicInt.Coe.ringHom (p := p)) r)
    (hcFE : ∀ (k : ℕ) (j : Fin d), ∃ r : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p),
      (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) * c (k + 1) j
        - ∑ m ∈ Finset.range (k + 1), ∑ l : Fin d,
            MvPolynomial.X (m, j, l) *
              ((⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p :
                  MvPolynomial (ℕ × Fin d × Fin d) (Padic p) →ₐ[Padic p] MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))^[m + 1]) (c (k - m) l)
        = (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) * MvPolynomial.map (PadicInt.Coe.ringHom (p := p)) r)
    (m : MvFormalGroup.CartierModule p
      (MvFormalGroup.map (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) Φ₀))
    (hm : ∀ (j : Fin d) (k n : ℕ),
      (coeff (Finsupp.single k (p ^ n)) (subst m.toPowerSeries (f j)) : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ k * c (k + n) j)
    (hm' : ∀ (j : Fin d) (e : ℕ →₀ ℕ), (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) →
      (coeff e (subst m.toPowerSeries (f j)) : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = 0) :
    ∃ m₀ : MvFormalGroup.CartierModule p Φ₀,
      MvFormalGroup.CartierModule.baseChange (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) m₀ = m := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_exists_baseChange_eq_of_coeff_subst_eq_ghost_of_functionalEquation.solution
