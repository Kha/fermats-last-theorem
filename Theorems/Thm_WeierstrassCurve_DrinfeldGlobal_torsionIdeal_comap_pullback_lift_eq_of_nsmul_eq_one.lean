import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_torsionIdeal_comap_pullback_lift_eq_of_nsmul_eq_one

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.torsionIdeal_comap_pullback_lift_eq_of_nsmul_eq_one
    {T : Type} [CommRing T] (W : WeierstrassCurve T)
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hcomm : ∀ {X : Scheme.{0}} (t : X ⟶ base (T := T)) (x y : SchemeHomOver t (projModelStrCR W)),
      G.mul t x y = G.mul t y x)
    (q : ℕ) (R : Section W) (hR : G.nsmul (𝟙 (base (T := T))) q R = G.one (𝟙 (base (T := T))))
    (τ : projModelCR W ≅ projModelCR W) (hτ : τ.hom ≫ projModelStrCR W = projModelStrCR W)
    (hτpt : ∀ {X : Scheme.{0}} (t : X ⟶ base (T := T)) (x : SchemeHomOver t (projModelStrCR W)),
      x.1 ≫ τ.hom = (G.mul t x (schemeHomOverComp t (Category.comp_id t) R)).1) :
    (torsionIdeal G q).comap (pullback.lift (pullback.fst (projModelStrCR W) (𝟙 (base (T := T))) ≫ τ.hom)
        (pullback.snd (projModelStrCR W) (𝟙 (base (T := T))))
        (by rw [Category.assoc, hτ]; exact pullback.condition)) = torsionIdeal G q := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_torsionIdeal_comap_pullback_lift_eq_of_nsmul_eq_one.solution
