import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_laurentBaseChange_qExpFunctionFieldC_coeffMap_apply_eq_of_slash_heckeDiagMatrix

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_algEquiv_laurentBaseChange_qExpFunctionFieldC_coeffMap_apply_eq_of_slash_heckeDiagMatrix
    (N : Subgroup SL(2, ℤ)) (hTN : ModularGroup.T ∈ N) (p : ℕ) [NeZero p] (γ γ' : SL(2, ℤ))
    (L : Type) [Field L] [CharZero L] (ι : L →+* ℂ)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ N))

    (hW : (∀ (k : ℤ) (f : ModularForm ((N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (p₀ : PowerSeries ℤ),
        ModularCurve.IsIntegralQExp (⇑f) p₀ →
        ∃ (D : ℤ) (n : ℕ) (c : Fin n → ℂ) (F : Fin n → ModularForm ((N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
          (r : Fin n → PowerSeries ℤ),
          D ≠ 0 ∧ (∀ i, c i ∈ ι.fieldRange) ∧ (∀ i, ModularCurve.IsIntegralQExp (⇑(F i)) (r i)) ∧
          ((D : ℂ) • (fun τ : UpperHalfPlane => ((⇑f) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))) = ∑ i, c i • (⇑(F i) : UpperHalfPlane → ℂ)))

    (hW' : (∀ (k : ℤ) (f : ModularForm ((N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (p₀ : PowerSeries ℤ),
        ModularCurve.IsIntegralQExp (⇑f) p₀ →
        ∃ (D : ℤ) (n : ℕ) (c : Fin n → ℂ) (F : Fin n → ModularForm ((N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
          (r : Fin n → PowerSeries ℤ),
          D ≠ 0 ∧ (∀ i, c i ∈ ι.fieldRange) ∧ (∀ i, ModularCurve.IsIntegralQExp (⇑(F i)) (r i)) ∧
          ((D : ℂ) • (fun τ : UpperHalfPlane => ((⇑f) ∣[k] γ') (ModularForm.heckeDiagMatrix p • τ))) = ∑ i, c i • (⇑(F i) : UpperHalfPlane → ℂ)))

    (u u' : ℤ → ℂ)
    (hcomp : ∀ (k : ℤ) (h : UpperHalfPlane → ℂ),
      (fun τ : UpperHalfPlane => ((fun τ : UpperHalfPlane => (h ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ∣[k] γ') (ModularForm.heckeDiagMatrix p • τ)) = u k • h)
    (hcomp' : ∀ (k : ℤ) (h : UpperHalfPlane → ℂ),
      (fun τ : UpperHalfPlane => ((fun τ : UpperHalfPlane => (h ∣[k] γ') (ModularForm.heckeDiagMatrix p • τ)) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) = u' k • h) :
    ∃ σ : ↥K ≃ₐ[L] ↥K,

      (∀ x : ↥K, ∃ (k : ℤ) (f g : ModularForm ((N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k),
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 ∧
        ModularCurve.coeffMap ι ((x : ↥K) : LaurentSeries L) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ∧
        (∃ (φ : ModularForm ((N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D : ℤ), D ≠ 0 ∧ (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun τ : UpperHalfPlane => ((⇑f) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))) ∧
        (∃ (ψ : ModularForm ((N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (E : ℤ), E ≠ 0 ∧ (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun τ : UpperHalfPlane => ((⇑g) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))) ∧
        (∃ (φ' : ModularForm ((N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D' : ℤ), D' ≠ 0 ∧ (⇑φ' : UpperHalfPlane → ℂ) = (D' : ℂ) • (fun τ : UpperHalfPlane => ((⇑f) ∣[k] γ') (ModularForm.heckeDiagMatrix p • τ))) ∧
        (∃ (ψ' : ModularForm ((N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (E' : ℤ), E' ≠ 0 ∧ (⇑ψ' : UpperHalfPlane → ℂ) = (E' : ℂ) • (fun τ : UpperHalfPlane => ((⇑g) ∣[k] γ') (ModularForm.heckeDiagMatrix p • τ)))) ∧

      (∀ (x : ↥K) (k : ℤ) (f g φ ψ : ModularForm ((N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun τ : UpperHalfPlane => ((⇑f) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun τ : UpperHalfPlane => ((⇑g) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥K) : LaurentSeries L) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((σ x : ↥K) : LaurentSeries L) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)) ∧

      (∀ (x : ↥K) (k : ℤ) (f g φ ψ : ModularForm ((N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun τ : UpperHalfPlane => ((⇑f) ∣[k] γ') (ModularForm.heckeDiagMatrix p • τ)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun τ : UpperHalfPlane => ((⇑g) ∣[k] γ') (ModularForm.heckeDiagMatrix p • τ)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥K) : LaurentSeries L) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((σ.symm x : ↥K) : LaurentSeries L) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)) ∧

      (∀ j : ↥K, ((j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L ModularCurve.jq →
        ((σ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_qExpFunctionFieldC_coeffMap_apply_eq_of_slash_heckeDiagMatrix.solution
