import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_eq_pt_of_le

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.ComplexPlaceDictionaryOf.restrictAlong_pt_eq_pt_of_le
    {Γ Γ' : Subgroup SL(2, ℤ)} (hle : Γ' ≤ Γ) (hT : ModularGroup.T ∈ Γ')
    {F₀ F₀' : IntermediateField ℚ (LaurentSeries ℚ)} (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀) (D' : ModularCurve.ComplexPlaceDictionaryOf Γ' F₀')
    (ι : ↥(ModularCurve.laurentBaseChange ℂ F₀) →ₐ[ℂ] ↥(ModularCurve.laurentBaseChange ℂ F₀'))
    (hι : ∀ x : ModularCurve.laurentBaseChange ℂ F₀,
      ((ι x : ModularCurve.laurentBaseChange ℂ F₀') : LaurentSeries ℂ) = (x : LaurentSeries ℂ))
    (hint : ι.toRingHom.IsIntegral) (τ : UpperHalfPlane) :
    (D'.pt τ).restrictAlong ι hint = D.pt τ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_restrictAlong_pt_eq_pt_of_le.solution
