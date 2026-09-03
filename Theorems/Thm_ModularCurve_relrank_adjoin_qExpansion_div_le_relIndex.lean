import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex

theorem ModularCurve.relrank_adjoin_qExpansion_div_le_relIndex
    (Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hle : Γ' ≤ Γ)
    (hT : ModularGroup.T ∈ Γ') (hind : Γ'.relIndex Γ ≠ 0) :
    IntermediateField.relrank
        (IntermediateField.adjoin ℂ {x : LaurentSeries ℂ | ∃ (k : ℤ)
            (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
            UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
              x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)})
        (IntermediateField.adjoin ℂ {x : LaurentSeries ℂ | ∃ (k : ℤ)
            (f g : ModularForm (Γ' : Subgroup (GL (Fin 2) ℝ)) k),
            UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
              x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)}) ≤
      (Γ'.relIndex Γ : Cardinal) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex.solution
