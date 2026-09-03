import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType

set_option autoImplicit false

p2m_open "AlgebraicCurve~finiteDimensional_adjoin_of_transcendental IntermediateField"

theorem AlgebraicCurve.IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    {t : F} (ht : Transcendental K t) :
    FiniteDimensional K⟮t⟯ F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType.solution
