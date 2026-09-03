import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_smul_algebraMap

set_option autoImplicit false
open scoped NumberField.PlaceDecomp
theorem NumberField.PlaceDecomp.smul_algebraMap (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (σ : NumberField.PlaceDecomp.decomp E K w) (x : K) :
    σ • algebraMap K (w.adicCompletion K) x = algebraMap K (w.adicCompletion K) ((σ : K ≃ₐ[E] K) x) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_smul_algebraMap.solution
