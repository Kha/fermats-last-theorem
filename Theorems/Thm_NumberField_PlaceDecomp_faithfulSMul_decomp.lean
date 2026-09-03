import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_faithfulSMul_decomp

set_option autoImplicit false
open scoped NumberField.PlaceDecomp
theorem NumberField.PlaceDecomp.faithfulSMul_decomp (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    FaithfulSMul (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_faithfulSMul_decomp.solution
