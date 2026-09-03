import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_comp_heckeAlphaBar_eq_heckeBetaBar
attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois
attribute [-simp] ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_algEquiv_comp_heckeAlphaBar_eq_heckeBetaBar
    (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ]
    (σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ))
    (hσ : IsAtkinLehnerAutFull N ℓ σ) :
    ∃ τ : laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) ≃ₐ[L]
        laurentBaseChange L (modularFunctionFieldFull (N * ℓ)),
      τ.toAlgHom.comp (heckeAlphaBar L N ℓ) = heckeBetaBar L N ℓ ∧
      τ.toAlgHom.comp (heckeBetaBar L N ℓ) = heckeAlphaBar L N ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_comp_heckeAlphaBar_eq_heckeBetaBar.solution
