import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_curveChange_heckeDegeneracy_rat
attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois
attribute [-simp] ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
  ModularCurve ModularCurve.XHDRLevel CongruenceSubgroup
open scoped MatrixGroups
set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.isFinite_flat_finrank_curveChange_heckeDegeneracy_rat
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (πα πβ : SchemeHomOver (toBase p (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) hj) (toBase p (ΓM M H) hj))
    [IsFinite πα.1] [IsFinite πβ.1] [LocallyOfFinitePresentation πα.1] [LocallyOfFinitePresentation πβ.1]
    (U : (X p (ΓM M H) hj).Opens)
    (hU : ∀ x : ↥(X p (ΓM M H) hj), ringKrullDim ((X p (ΓM M H) hj).presheaf.stalk x) ≤ 1 → x ∈ U)
    [Flat (πα.1 ∣_ U)] [Flat (πβ.1 ∣_ U)]
    (hrkα : ∀ y : ↥(X p (ΓM M H) hj), y ∈ U → πα.1.finrank y = (if ℓ ∣ M then ℓ else ℓ + 1))
    (hrkβ : ∀ y : ↥(X p (ΓM M H) hj), y ∈ U → πβ.1.finrank y = (if ℓ ∣ M then ℓ else ℓ + 1)) :
    ∃ (_ : IsFinite (RelPicard.curveChange πα.1 πα.2 (SmoothProperCurve.specMap (R p) ℚ)))
      (_ : IsFinite (RelPicard.curveChange πβ.1 πβ.2 (SmoothProperCurve.specMap (R p) ℚ)))
      (_ : LocallyOfFinitePresentation (RelPicard.curveChange πα.1 πα.2 (SmoothProperCurve.specMap (R p) ℚ)))
      (_ : LocallyOfFinitePresentation (RelPicard.curveChange πβ.1 πβ.2 (SmoothProperCurve.specMap (R p) ℚ))),
      Flat (RelPicard.curveChange πα.1 πα.2 (SmoothProperCurve.specMap (R p) ℚ)) ∧
      Flat (RelPicard.curveChange πβ.1 πβ.2 (SmoothProperCurve.specMap (R p) ℚ)) ∧
      (∀ y, (RelPicard.curveChange πα.1 πα.2 (SmoothProperCurve.specMap (R p) ℚ)).finrank y = (if ℓ ∣ M then ℓ else ℓ + 1)) ∧
      (∀ y, (RelPicard.curveChange πβ.1 πβ.2 (SmoothProperCurve.specMap (R p) ℚ)).finrank y = (if ℓ ∣ M then ℓ else ℓ + 1)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_curveChange_heckeDegeneracy_rat.solution
