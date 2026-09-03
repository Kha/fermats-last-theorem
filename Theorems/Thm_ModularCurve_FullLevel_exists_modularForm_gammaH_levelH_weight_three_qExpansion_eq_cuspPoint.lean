import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_three_qExpansion_eq_cuspPoint
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_weight_three_qExpansion_eq_cuspPoint
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ q)
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / q)) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    letI ξu : Lˣ := (hξ.isUnit (Fact.out : q.Prime).ne_zero).unit
    ∃ Rw : (Fin 2 → ZMod q) → ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
            Subgroup (GL (Fin 2) ℝ)) 3,
      (∀ v : Fin 2 → ZMod q, v ≠ 0 →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑(Rw v))) =
          ModularCurve.coeffMap ι (2 * (ModularCurve.cuspPoint L q ξu v).2 + (ModularCurve.cuspPoint L q ξu v).1)) ∧
      (∀ ρ : SL(2, ℤ), ρ ∈ CongruenceSubgroup.Gamma0 M' → ∀ v : Fin 2 → ZMod q,
        (⇑(Rw v) ∣[(3 : ℤ)] ModularCurve.FullLevel.conjElemN q ρ) =
          ⇑(Rw ![v 0 * ((ρ 1 1 : ℤ) : ZMod q) + v 1 * ((ρ 0 1 : ℤ) : ZMod q),
                  v 0 * ((ρ 1 0 : ℤ) : ZMod q) + v 1 * ((ρ 0 0 : ℤ) : ZMod q)])) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_three_qExpansion_eq_cuspPoint.solution
