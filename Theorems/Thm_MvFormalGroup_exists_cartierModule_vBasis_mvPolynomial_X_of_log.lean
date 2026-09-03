import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import P2M.Util
import P2M.Sol.S_MvFormalGroup_exists_cartierModule_vBasis_mvPolynomial_X_of_log
attribute [-instance] MvFormalGroup.instIsCommMapRingHom
attribute [-simp] MvFormalGroup.CartierModule.toPowerSeries_baseChangeEqFun MvFormalGroup.toPowerSeries_map_ringHom MvFormalGroup.CartierModule.toPowerSeries_baseChangeEq

set_option autoImplicit false

universe u

theorem MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X_of_log
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
    (h5 : ∀ i : Fin d,
      MvPowerSeries.subst (MvFormalGroup.map (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) Φ₀).toPowerSeries (f i)
        = MvPowerSeries.subst (fun j => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))) (f i)
          + MvPowerSeries.subst (fun j => MvPowerSeries.X (Sum.inr j)) (f i)) :
    ∃ (γ : Fin d → MvFormalGroup.CartierModule p Φ₀),
      IsUnit (Matrix.of fun i k => MvFormalGroup.CartierModule.tangent (γ i) k).det ∧
      ∀ (i : Fin d) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p Φ₀,
        MvFormalGroup.CartierModule.frobenius (γ i) =
          (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ₀)))^[(m : ℕ)]
            (∑ j : Fin d, MvFormalGroup.CartierModule.homothety
              (MvPolynomial.X ((m : ℕ), j, i) : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)) (γ j))) +
          (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ₀)))^[N] h := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_exists_cartierModule_vBasis_mvPolynomial_X_of_log.solution
