import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_RelativeGroupLaw_basisDivisorOver_comap_mapOnProdOver

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.RelativeGroupLaw.basisDivisorOver_comap_mapOnProdOver
    {R : Type u} [CommRing R] {V : WeierstrassCurve.Projective R}
    (G : RelativeGroupLaw R (projModelStrCR V)) (q : ℕ)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P Q : SchemeHomOver t (projModelStrCR V)) :
    (G.basisDivisorOver q t P Q).comap (mapOnProdOver (projModelStrCR V) ψ hψ) =
        G.basisDivisorOver q t' (schemeHomOverComp ψ hψ P) (schemeHomOverComp ψ hψ Q) ∧
      (G.torsionIdealOver q t).comap (mapOnProdOver (projModelStrCR V) ψ hψ) = G.torsionIdealOver q t' := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_RelativeGroupLaw_basisDivisorOver_comap_mapOnProdOver.solution
