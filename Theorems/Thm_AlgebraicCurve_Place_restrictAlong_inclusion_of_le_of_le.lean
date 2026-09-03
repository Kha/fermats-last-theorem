import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_restrictAlong_inclusion_of_le_of_le

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.restrictAlong_inclusion_of_le_of_le
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    {S T : IntermediateField K E} (hST : S ≤ T) (hTS : T ≤ S)
    (h : (IntermediateField.inclusion hST).toRingHom.IsIntegral)
    (h' : (IntermediateField.inclusion hTS).toRingHom.IsIntegral) :
    (∀ w : Place K T, (w.restrictAlong (IntermediateField.inclusion hST) h).restrictAlong (IntermediateField.inclusion hTS) h' = w) ∧
    (∀ v : Place K S, (v.restrictAlong (IntermediateField.inclusion hTS) h').restrictAlong (IntermediateField.inclusion hST) h = v) ∧
    (∀ w : Place K T, w.ramificationIndexAlong (IntermediateField.inclusion hST) = 1) ∧
    (∀ (w : Place K T) (f : S), (w.restrictAlong (IntermediateField.inclusion hST) h).ord f = w.ord (IntermediateField.inclusion hST f)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_restrictAlong_inclusion_of_le_of_le.solution
