import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_a2_checks_crossYZ

open WeierstrassProjModel MvPolynomial

theorem WeierstrassProjModel.kw_a2_checks_crossYZ.{u} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (F : Type u) [Field F] [Algebra R F] :
    (∀ P : Fin 3 → F, ((W.baseChange F).toProjective).Equation P →
      MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_Y W) * ((W.baseChange F).toProjective).dblZ P
      = MvPolynomial.aeval (Sum.elim P P) (kw_lrSym_Z W) * ((W.baseChange F).toProjective).dblY P) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_a2_checks_crossYZ.solution
