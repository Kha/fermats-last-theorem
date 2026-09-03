import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_eq_of_comap_toValuationSubring_eq_of_isRational
set_option autoImplicit false

noncomputable section

open AlgebraicCurve

theorem
AlgebraicCurve.Place.eq_of_comap_toValuationSubring_eq_of_isRational
    {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F'] [Algebra K F] [Algebra K' F'] [Algebra K K']
    [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (V : Place K F) (hV : V.IsRational) (w w' : Place K' F')
    (hw : w.toValuationSubring.comap (algebraMap F F') = V.toValuationSubring)
    (hw' : w'.toValuationSubring.comap (algebraMap F F') = V.toValuationSubring) :
    w = w' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_eq_of_comap_toValuationSubring_eq_of_isRational.solution

end
