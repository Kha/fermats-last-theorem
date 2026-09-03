import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary
attribute [-simp] ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (h : ℕ) (hh : 0 < h)
    (hT : ModularGroup.T ^ h ∈ Γ) (hS : ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ ∈ Γ)
    (R : Subring ℂ) {k w : ℤ} (hkw : Even (k + w))
    (G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hG : ∀ n : ℕ, (UpperHalfPlane.qExpansion (h : ℝ) (⇑G : UpperHalfPlane → ℂ)).coeff n ∈ R)
    (Θ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) w)
    (hΘ : ∀ n : ℕ, (UpperHalfPlane.qExpansion (h : ℝ) (⇑Θ : UpperHalfPlane → ℂ)).coeff n ∈ R)
    (m₀ : ℕ) (hm₀ : w < 12 * (m₀ : ℤ))
    (hΘS₀ : ∀ n : ℕ, n < m₀ → (UpperHalfPlane.qExpansion 1
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n = 0)
    (hΘS₁ : ∃ v ∈ R, v * (UpperHalfPlane.qExpansion 1
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff m₀ = 1)
    (hΘS : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n ∈ R)
    (δ : ℝ) (hδ : 0 < δ)
    (hdecay : ∀ β : SL(2, ℤ),
      (∀ j : ℤ, β * ModularGroup.T ^ j ∉ Γ ∧ -(β * ModularGroup.T ^ j) ∉ Γ) →
      (β * ModularGroup.S⁻¹ ∉ Γ ∧ -(β * ModularGroup.S⁻¹) ∉ Γ) →
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] (β : GL (Fin 2) ℝ)) =O[UpperHalfPlane.atImInfty]
        fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * ((m₀ : ℝ) + δ)) * τ.im))
    (n : ℕ) :
    (UpperHalfPlane.qExpansion 1
      ((⇑G : UpperHalfPlane → ℂ) ∣[k] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n ∈ R := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary.solution
