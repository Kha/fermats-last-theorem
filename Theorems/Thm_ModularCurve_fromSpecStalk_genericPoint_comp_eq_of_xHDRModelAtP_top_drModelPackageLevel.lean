import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_DRModelPackageLevel
import P2M.Util
import P2M.Sol.S_ModularCurve_fromSpecStalk_genericPoint_comp_eq_of_xHDRModelAtP_top_drModelPackageLevel

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.fromSpecStalk_genericPoint_comp_eq_of_xHDRModelAtP_top_drModelPackageLevel
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) [NeZero (N₀ * p)]
    (hpM : p ∣ N₀ * p) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p (N₀ * p) ⊤ hpM hj) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (hF : xHFunctionFieldBar (N₀ * p) ⊤ = modularFunctionFieldBar (N₀ * p))
    (e : IgusaScheme (N₀ * p) p ≅ XHDRLevel.X p (XHDRLevel.ΓM (N₀ * p) ⊤) hj)
    (eFin : ↥(IgusaScheme.chartAlgFin (N₀ * p) p) →+* ↥(XHDRLevel.chartAlgFin p (XHDRLevel.ΓM (N₀ * p) ⊤) hj))
    (hFin : ∀ x : ↥(IgusaScheme.chartAlgFin (N₀ * p) p),
      (((eFin x : ↥(XHDRLevel.chartAlgFin p (XHDRLevel.ΓM (N₀ * p) ⊤) hj)) : ↥(qExpFunctionFieldC ℚ (XHDRLevel.ΓM (N₀ * p) ⊤))) :
          LaurentSeries ℚ) = ((x : ↥(modularFunctionFieldFull (N₀ * p))) : LaurentSeries ℚ))
    (hbase : e.hom ≫ XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj = IgusaScheme.igusaTo (N₀ * p) p)
    (hcFin : Spec.map (CommRingCat.ofHom eFin) ≫ IgusaScheme.ιFin (N₀ * p) p = XHDRLevel.ιFin p (XHDRLevel.ΓM (N₀ * p) ⊤) hj ≫ e.inv)
    (ψ : 𝔛.Meta.C ⟶ 𝔓.Meta.C)
    (hψ₁ : ψ ≫ 𝔓.eeta ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _ ≫ e.inv)
    (hψ₂ : ψ ≫ 𝔓.Meta.toBase = 𝔛.Meta.toBase) :
    𝔛.Meta.C.fromSpecStalk (genericPoint 𝔛.Meta.C) ≫ ψ =
      Spec.map (CommRingCat.ofHom
        (𝔛.Meta.ffEquiv.toRingHom.comp
          ((IntermediateField.equivOfEq hF).toRingEquiv.symm.toRingHom.comp 𝔓.Meta.ffEquiv.symm.toRingHom))) ≫
        𝔓.Meta.C.fromSpecStalk (genericPoint 𝔓.Meta.C) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_fromSpecStalk_genericPoint_comp_eq_of_xHDRModelAtP_top_drModelPackageLevel.solution
