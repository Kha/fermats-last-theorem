import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_VariableChangeSeries
import Theorems.Thm_WeierstrassCurve_coeff_one_variableChangeSeries_and_subst_formalGroupLawFixed
import P2M.Util
namespace P2MW.S_FormalGroup_exists_lawHom_series_eq_variableChangeSeries
attribute [-instance] WeierstrassCurve.instIsCommFormalGroup
attribute [-simp] WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

set_option autoImplicit false

universe u

open FormalGroup IsLocalRing

theorem solution
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R)
    (F₁ F₂ : FormalGroup R) (h₁ : F₁.toPowerSeries = W.formalGroupLawFixed)
    (h₂ : F₂.toPowerSeries = (C • W).formalGroupLawFixed) :
    ∃ σ : FormalGroup.LawHom F₁ F₂, σ.series = W.variableChangeSeries C := by
  refine ⟨{ series := W.variableChangeSeries C
            constantCoeff_series := W.constantCoeff_variableChangeSeries C
            comm := ?_ }, rfl⟩
  rw [h₁, h₂]
  exact (W.coeff_one_variableChangeSeries_and_subst_formalGroupLawFixed C).2
