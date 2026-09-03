import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_RelativeGroupLaw_IsDrinfeldBasisOver_exists_comp_fst_schemeKer_eq

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.RelativeGroupLaw.IsDrinfeldBasisOver.exists_comp_fst_schemeKer_eq
    {R : Type u} [CommRing R] {V : WeierstrassCurve.Projective R}
    (G : RelativeGroupLaw R (projModelStrCR V)) {q : ℕ} (hq : 2 ≤ q)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {P Q : SchemeHomOver t (projModelStrCR V)}
    (h : G.IsDrinfeldBasisOver q t P Q) :
    (∃ p : T ⟶ G.schemeKer q, p ≫ pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1 = P.1) ∧
      ∃ p : T ⟶ G.schemeKer q, p ≫ pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1 = Q.1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_RelativeGroupLaw_IsDrinfeldBasisOver_exists_comp_fst_schemeKer_eq.solution
