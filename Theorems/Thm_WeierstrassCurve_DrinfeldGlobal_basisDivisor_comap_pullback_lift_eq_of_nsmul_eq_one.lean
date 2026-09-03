import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_basisDivisor_comap_pullback_lift_eq_of_nsmul_eq_one

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.basisDivisor_comap_pullback_lift_eq_of_nsmul_eq_one
    {T : Type} [CommRing T] (W : WeierstrassCurve T)
    (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ)
    (P Q : Section W) (hQ : G.nsmul (𝟙 (base (T := T))) q Q = G.one (𝟙 (base (T := T))))
    (τ : projModelCR W ≅ projModelCR W) (hτ : τ.hom ≫ projModelStrCR W = projModelStrCR W)
    (hτpt : ∀ {X : Scheme.{0}} (t : X ⟶ base (T := T)) (x : SchemeHomOver t (projModelStrCR W)),
      x.1 ≫ τ.hom = (G.mul t x (schemeHomOverComp t (Category.comp_id t) Q)).1) :
    (basisDivisor G q P Q).comap (pullback.lift (pullback.fst (projModelStrCR W) (𝟙 (base (T := T))) ≫ τ.hom)
        (pullback.snd (projModelStrCR W) (𝟙 (base (T := T))))
        (by rw [Category.assoc, hτ]; exact pullback.condition)) = basisDivisor G q P Q := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_basisDivisor_comap_pullback_lift_eq_of_nsmul_eq_one.solution
