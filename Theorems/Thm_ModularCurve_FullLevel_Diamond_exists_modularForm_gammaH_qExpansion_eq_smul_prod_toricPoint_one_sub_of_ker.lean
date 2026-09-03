import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_Diamond_exists_modularForm_gammaH_qExpansion_eq_smul_prod_toricPoint_one_sub_of_ker
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.FullLevel.Diamond.exists_modularForm_gammaH_qExpansion_eq_smul_prod_toricPoint_one_sub_of_ker
    (M' : ℕ) [NeZero M'] (ℓg : ℕ) (hℓg : 3 ≤ ℓg) (hℓgM' : ℓg ∣ M')
    (Hb : Subgroup (ZMod M')ˣ) (hHb : Hb = (ZMod.unitsMap hℓgM').ker)
    (p k : ℕ) [Fact p.Prime] (hpk : p ^ k ∣ M')
    (t : ℕ) (ht : t.Coprime ℓg) (c : ℚ) :
    ∃ (Φ Ψ : ModularForm (CohCarrier.GammaH M' Hb :
        Subgroup (GL (Fin 2) ℝ)) (2 * (((Finset.Icc 1 (p ^ k / 2)).filter (fun i => ¬ p ∣ i)).card : ℕ) : ℤ))
      (a : ℚ), a ≠ 0 ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Ψ) =
        (a : ℂ) • ((ModularCurve.toricPoint ℂ 1 (Complex.exp (2 * Real.pi * Complex.I / ℓg) ^ t)).1 -
          (ModularCurve.toricPoint ℂ 1 (Complex.exp (2 * Real.pi * Complex.I / ℓg) ^ (2 * t))).1) ^
            ((Finset.Icc 1 (p ^ k / 2)).filter (fun i => ¬ p ∣ i)).card ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Φ) =
        (a : ℂ) • ∏ i ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun i => ¬ p ∣ i),
          ((c : ℂ) • ((ModularCurve.toricPoint ℂ 1 (Complex.exp (2 * Real.pi * Complex.I / ℓg) ^ t)).1 -
              (ModularCurve.toricPoint ℂ 1 (Complex.exp (2 * Real.pi * Complex.I / ℓg) ^ (2 * t))).1) -
            ((ModularCurve.toricPoint ℂ 1 (Complex.exp (2 * Real.pi * Complex.I / ((p ^ k : ℕ) : ℂ)) ^ i)).1 -
              (ModularCurve.toricPoint ℂ 1 (Complex.exp (2 * Real.pi * Complex.I / ℓg) ^ t)).1)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_gammaH_qExpansion_eq_smul_prod_toricPoint_one_sub_of_ker.solution
