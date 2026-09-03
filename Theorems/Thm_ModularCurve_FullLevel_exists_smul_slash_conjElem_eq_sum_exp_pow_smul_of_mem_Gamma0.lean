import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_exists_smul_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel

open scoped MatrixGroups ModularForm

theorem ModularCurve.FullLevel.exists_smul_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (hqM' : ¬ q ∣ M') {k : ℤ} (hk : Even k)
    (f : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
      Subgroup (GL (Fin 2) ℝ)) k)
    (pf : PowerSeries ℤ) (hf : ModularCurve.IsIntegralQExp f pf)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') :
    ∃ D : ℤ, D ≠ 0 ∧
      ∃ (h : ℕ → ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
          Subgroup (GL (Fin 2) ℝ)) k) (p : ℕ → PowerSeries ℤ),
        (∀ j : ℕ, ModularCurve.IsIntegralQExp (h j) (p j)) ∧
        ∀ (s : ℕ) (γ' : SL(2, ℤ)), Nat.Coprime s q → γ' ∈ CongruenceSubgroup.Gamma0 M' →
          !![(1 : ZMod q), 0; 0, (s : ZMod q)] * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q)
            = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) * !![(1 : ZMod q), 0; 0, (s : ZMod q)] →
          (D : ℂ) • ((⇑f : UpperHalfPlane → ℂ) ∣[k] ModularCurve.FullLevel.conjElem q γ') =
            ∑ j ∈ Finset.range q,
              Complex.exp (2 * Real.pi * Complex.I * ((s * j : ℕ) : ℂ) / q) •
                (⇑(h j) : UpperHalfPlane → ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_exists_smul_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0.solution
