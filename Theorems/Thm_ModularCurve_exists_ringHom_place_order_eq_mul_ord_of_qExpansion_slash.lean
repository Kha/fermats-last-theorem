import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

theorem ModularCurve.exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (σ : SL(2, ℤ)) :
    ∃ (Φ : ModularCurve.laurentBaseChange ℂ F₀ →+* LaurentSeries ℂ)
      (P : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ F₀)) (e : ℕ),
      0 < e ∧
      (∀ x : ModularCurve.laurentBaseChange ℂ F₀, x ∈ P.toValuationSubring ↔ 0 ≤ (Φ x).order) ∧
      (∀ x : ModularCurve.laurentBaseChange ℂ F₀, x ∈ P.toValuationSubring ↔
        ∃ L : ℂ, Filter.Tendsto
          (fun τ : UpperHalfPlane => ModularCurve.realizeOf Γ (x : LaurentSeries ℂ) (σ • τ)) atImInfty (𝓝 L)) ∧
      (∀ (x : ModularCurve.laurentBaseChange ℂ F₀) (k : ℤ)
          (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k), h ≠ 0 →
        (x : LaurentSeries ℂ) *
            ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) →
        Φ x * ((UpperHalfPlane.qExpansion (Γ.normalCore.index : ℝ)
              ((h : UpperHalfPlane → ℂ) ∣[k] σ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((UpperHalfPlane.qExpansion (Γ.normalCore.index : ℝ)
              ((g : UpperHalfPlane → ℂ) ∣[k] σ) : PowerSeries ℂ) : LaurentSeries ℂ)) ∧
      (∀ c : ℂ, Φ (algebraMap ℂ (ModularCurve.laurentBaseChange ℂ F₀) c) = HahnSeries.C c) ∧
      (∀ x : ModularCurve.laurentBaseChange ℂ F₀, x ≠ 0 → (Φ x).order = e * P.ord x) ∧
      (∀ y : ModularCurve.laurentBaseChange ℂ F₀, (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ →
        (Φ y).order = -(Γ.normalCore.index : ℤ) ∧ (e : ℤ) * P.ord y = -(Γ.normalCore.index : ℤ) ∧
          y ∉ P.toValuationSubring) ∧
      (∀ x : ModularCurve.laurentBaseChange ℂ F₀, x ≠ 0 → ∃ L : ℂ, L ≠ 0 ∧
        Filter.Tendsto
          (fun τ : UpperHalfPlane => ModularCurve.realizeOf Γ (x : LaurentSeries ℂ) (σ • τ) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((e : ℤ) * P.ord x : ℂ) * (τ : ℂ) / (Γ.normalCore.index : ℂ))))
          atImInfty (𝓝 L)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash.solution
