import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemistableModel_isReduced_stalk_quotient_maximalIdeal_of_base_eq_closedPoint

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

theorem AlgebraicCurve.SemistableModel.isReduced_stalk_quotient_maximalIdeal_of_base_eq_closedPoint
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (x : M.X) (hx : M.toBase.base x = IsLocalRing.closedPoint ↥A) :
    _root_.IsReduced (M.X.presheaf.stalk x ⧸
      Ideal.map ((M.X.presheaf.germ ⊤ x trivial).hom.comp
        (M.toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom))
        (IsLocalRing.maximalIdeal ↥A)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemistableModel_isReduced_stalk_quotient_maximalIdeal_of_base_eq_closedPoint.solution
