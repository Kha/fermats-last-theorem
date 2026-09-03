import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_coeff_nthSeries_eq_mul_hasseInvariant
attribute [-simp] FormalGroup.LawIso.mk.sizeOf_spec FormalGroup.LawHom.mk.sizeOf_spec FormalGroup.LawHom.mk.injEq FormalGroup.LawIso.mk.injEq ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ

set_option autoImplicit false

open FormalGroup

theorem WeierstrassCurve.exists_coeff_nthSeries_eq_mul_hasseInvariant
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    ∃ c : ℤ, ((c : ZMod q) ≠ 0) ∧
      ∀ (R : Type) [CommRing R] [CharP R q] (W : WeierstrassCurve R), IsUnit W.Δ → ∀ (G : FormalGroup R),
        G.toPowerSeries = W.formalGroupLawFixed →
          PowerSeries.coeff q (G.nthSeries q) = (c : R) * W.hasseInvariant q := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_coeff_nthSeries_eq_mul_hasseInvariant.solution
