import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_exists_lawIso_appAdic_originParam_eq_of_variableChange_map_eq_one
attribute [-instance] WeierstrassCurve.instIsCommFormalGroup
attribute [-simp] WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero FormalGroup.DrinfeldLevel.mk.sizeOf_spec FormalGroup.DrinfeldLevel.mk.injEq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_lawIso_appAdic_originParam_eq_of_variableChange_map_eq_one
    {T : Type u} [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T]
    {k : Type u} [Field k] (resT : T →+* k) (hsT : Function.Surjective resT) (hkT : RingHom.ker resT = maximalIdeal T)
    (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T) (hC1 : C.map resT = 1)
    (W' : WeierstrassCurve T) (hW' : W' = C • W)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hvc : IsVariableChangeHom W C φ)
    (P Q : Section W) (χP χQ : OriginChartRing W →+* T)
    (hP : ReducesToOrigin P χP (maximalIdeal T)) (hQ : ReducesToOrigin Q χQ (maximalIdeal T))
    (P' Q' : Section W') (χP' χQ' : OriginChartRing W' →+* T)
    (hP' : ReducesToOrigin P' χP' (maximalIdeal T)) (hQ' : ReducesToOrigin Q' χQ' (maximalIdeal T))
    (hPP' : P'.1 ≫ eqToHom (congrArg projModelCR hW') ≫ Proj.map φ hφ = P.1)
    (hQQ' : Q'.1 ≫ eqToHom (congrArg projModelCR hW') ≫ Proj.map φ hφ = Q.1)
    (F' : FormalGroup T) (hF' : F'.toPowerSeries = W.formalGroupLawFixed)
    (GT : FormalGroup T) (hGT : GT.toPowerSeries = W'.formalGroupLawFixed)
    (G : FormalGroup T) (ψ : FormalGroup.LawIso GT G)
    (hψ : ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0)
    (y₀ y₁ : T)
    (hy₀ : ψ.toLawHom.appAdic (maximalIdeal T) (originParam χP') = y₀)
    (hy₁ : ψ.toLawHom.appAdic (maximalIdeal T) (originParam χQ') = y₁) :
    ∃ ψ' : FormalGroup.LawIso F' G,
      (∀ n : ℕ, resT (PowerSeries.coeff n ψ'.series) = if n = 1 then 1 else 0) ∧
      ψ'.toLawHom.appAdic (maximalIdeal T) (originParam χP) = y₀ ∧
      ψ'.toLawHom.appAdic (maximalIdeal T) (originParam χQ) = y₁ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_lawIso_appAdic_originParam_eq_of_variableChange_map_eq_one.solution
