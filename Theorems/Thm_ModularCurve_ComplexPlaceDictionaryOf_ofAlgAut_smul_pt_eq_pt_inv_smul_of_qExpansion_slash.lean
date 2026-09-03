import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul_of_qExpansion_slash

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.ComplexPlaceDictionaryOf.ofAlgAut_smul_pt_eq_pt_inv_smul_of_qExpansion_slash
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀)
    (α : GL (Fin 2) ℝ) (hα : 0 < (α.det : ℝ))
    (hTα : α * (ModularGroup.T : GL (Fin 2) ℝ) * α⁻¹ ∈ (Γ : Subgroup (GL (Fin 2) ℝ)))
    (σ : ↥(ModularCurve.laurentBaseChange ℂ F₀) ≃ₐ[ℂ] ↥(ModularCurve.laurentBaseChange ℂ F₀))
    (hσ : ∀ (k : ℤ) (f g : ModularForm Γ k) (pf pg : PowerSeries ℤ),
        ModularCurve.IsIntegralQExp f pf → ModularCurve.IsIntegralQExp g pg →
        ModularCurve.intSeriesC ℚ pg ≠ 0 →
        ∀ y : ↥(ModularCurve.laurentBaseChange ℂ F₀),
          (y : LaurentSeries ℂ) =
            ModularCurve.coeffEmb ℂ (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg) →
          ((σ y : ↥(ModularCurve.laurentBaseChange ℂ F₀)) : LaurentSeries ℂ) *
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] α)) =
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] α)))
    (τ : UpperHalfPlane) :
    AlgebraicCurve.SemilinearAut.ofAlgAut σ • D.pt τ = D.pt (α⁻¹ • τ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_ofAlgAut_smul_pt_eq_pt_inv_smul_of_qExpansion_slash.solution
