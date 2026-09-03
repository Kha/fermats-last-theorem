import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_existsUnique_schemeHomOver_barPt_comp_eq_of_isProper

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.existsUnique_schemeHomOver_barPt_comp_eq_of_isProper
    {p : ℕ} {X : Scheme.{0}} (f : X ⟶ base p) [IsProper f]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ρ : baseRing p →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap (baseRing p) (AlgebraicClosure ℚ))
    (pt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X) (hpt : pt ≫ f = genPt p) :
    ∃! s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) f, barPt A ≫ s.1 = pt := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_existsUnique_schemeHomOver_barPt_comp_eq_of_isProper.solution
