import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_Diamond_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.FullLevel.Diamond.exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)

    (p k : ℕ) [Fact p.Prime] (hpk : p ^ k ∣ M') (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    ∀ j : ℕ, j ≤ ModularCurve.gamma0PowDeg p k →
      ∃ S : ModularForm (CohCarrier.GammaH (q ^ 2 * M') H₁ :
            Subgroup (GL (Fin 2) ℝ)) (2 * ((ModularCurve.gamma0PowDeg p k - j : ℕ) : ℤ)),
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑S)) =
          (∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a),
            (Polynomial.X - Polynomial.C ((ModularCurve.toricPoint ℂ q (ζ ^ a)).1 + HahnSeries.C ((12 : ℂ)⁻¹)))).coeff j ∧
        ∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' →
          (⇑S ∣[(2 * ((ModularCurve.gamma0PowDeg p k - j : ℕ) : ℤ))] ModularCurve.FullLevel.conjElemN q ρ) = ⇑S := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_Diamond_exists_modularForm_qExpansion_eq_coeff_toricGenKernel_and_slash_conjElemN_eq.solution
