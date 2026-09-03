import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_qExpansion_eq_smul_prod_toricPoint_sub_gamma0Pow
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_qExpansion_eq_smul_prod_toricPoint_sub_gamma0Pow
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (M : ℕ) [NeZero M] (p k : ℕ) [Fact p.Prime] (hpk : p ^ k ∣ M)
    (t : ℕ) (ht : t.Coprime N) (c : ℚ) :
    ∃ (Φ Ψ : ModularForm (CohCarrier.GammaH (N ^ 2 * M) (ModularCurve.FullLevel.levelH N M) :
        Subgroup (GL (Fin 2) ℝ)) (2 * (((Finset.Icc 1 (p ^ k / 2)).filter (fun i => ¬ p ∣ i)).card : ℕ) : ℤ))
      (a : ℚ), a ≠ 0 ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Ψ) =
        (a : ℂ) • ((ModularCurve.toricPoint ℂ N (Complex.exp (2 * Real.pi * Complex.I / N) ^ t)).1 -
          (ModularCurve.toricPoint ℂ N (Complex.exp (2 * Real.pi * Complex.I / N) ^ (2 * t))).1) ^
            ((Finset.Icc 1 (p ^ k / 2)).filter (fun i => ¬ p ∣ i)).card ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Φ) =
        (a : ℂ) • ∏ i ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun i => ¬ p ∣ i),
          ((c : ℂ) • ((ModularCurve.toricPoint ℂ N (Complex.exp (2 * Real.pi * Complex.I / N) ^ t)).1 -
              (ModularCurve.toricPoint ℂ N (Complex.exp (2 * Real.pi * Complex.I / N) ^ (2 * t))).1) -
            ((ModularCurve.toricPoint ℂ N (Complex.exp (2 * Real.pi * Complex.I / ((p ^ k : ℕ) : ℂ)) ^ i)).1 -
              (ModularCurve.toricPoint ℂ N (Complex.exp (2 * Real.pi * Complex.I / N) ^ t)).1)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_qExpansion_eq_smul_prod_toricPoint_sub_gamma0Pow.solution
