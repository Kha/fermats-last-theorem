import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_qExpand

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.ComplexPlaceDictionaryOf.restrictAlong_pt_qExpand
    (Γ Γ' : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ) (hT' : ModularGroup.T ∈ Γ')
    (ℓ : ℕ) [NeZero ℓ] (hΓ' : Γ' ≤ CongruenceSubgroup.conjGL Γ (ModularForm.heckeDiagMatrix ℓ))
    (F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ))
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀) (D' : ModularCurve.ComplexPlaceDictionaryOf Γ' F₁)
    (β : ModularCurve.laurentBaseChange ℂ F₀ →ₐ[ℂ] ModularCurve.laurentBaseChange ℂ F₁)
    (hβq : ∀ x : ModularCurve.laurentBaseChange ℂ F₀,
      ((β x : ModularCurve.laurentBaseChange ℂ F₁) : LaurentSeries ℂ) =
        ModularCurve.qExpand ℂ ℓ (x : LaurentSeries ℂ))
    (hβ : β.toRingHom.IsIntegral) (τ : UpperHalfPlane) :
    (D'.pt τ).restrictAlong β hβ = D.pt (ModularForm.heckeDiagMatrix ℓ • τ) ∧
      D'.ramification τ * (D'.pt τ).ramificationIndexAlong β =
        D.ramification (ModularForm.heckeDiagMatrix ℓ • τ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_qExpand.solution
