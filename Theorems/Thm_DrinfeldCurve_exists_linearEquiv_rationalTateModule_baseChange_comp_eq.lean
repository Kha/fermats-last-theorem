import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_ModularCurve_JZeroTateModule
import Mathlib.RepresentationTheory.Basic
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_exists_linearEquiv_rationalTateModule_baseChange_comp_eq

set_option autoImplicit false

open scoped TensorProduct

namespace DrinfeldCurve

theorem exists_linearEquiv_rationalTateModule_baseChange_comp_eq
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (CoordRing q k)]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type*) [Field E] [Algebra ℚ_[ℓ] E] (E' : Type*) [Field E'] [Algebra ℚ_[ℓ] E'] [Algebra E E']
    [IsScalarTower ℚ_[ℓ] E E'] :
    let ρE : Representation E (hSubgroup q)
        (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) :=
      (Module.End.baseChangeHom ℚ_[ℓ] E
          (ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) :
        Module.End ℚ_[ℓ]
            (ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) →*
          Module.End E (E ⊗[ℚ_[ℓ]]
            ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)))).comp
        ((ModularCurve.rationalGaloisRep ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))
            (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k)).comp (hFunctionFieldAction q k))
    let ρE' : Representation E' (hSubgroup q)
        (E' ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) :=
      (Module.End.baseChangeHom ℚ_[ℓ] E'
          (ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) :
        Module.End ℚ_[ℓ]
            (ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))) →*
          Module.End E' (E' ⊗[ℚ_[ℓ]]
            ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)))).comp
        ((ModularCurve.rationalGaloisRep ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))
            (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k)).comp (hFunctionFieldAction q k))
    ∃ e : (E' ⊗[E] (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
          (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)))) ≃ₗ[E']
        (E' ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))),
      ∀ h : hSubgroup q, e.toLinearMap ∘ₗ (ρE h).baseChange E' = ρE' h ∘ₗ e.toLinearMap := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_exists_linearEquiv_rationalTateModule_baseChange_comp_eq.solution
