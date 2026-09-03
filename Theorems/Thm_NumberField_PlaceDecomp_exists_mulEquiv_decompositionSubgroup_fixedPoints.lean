import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_exists_mulEquiv_decompositionSubgroup_fixedPoints

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp
theorem NumberField.PlaceDecomp.exists_mulEquiv_decompositionSubgroup_fixedPoints (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K)) [Finite (NumberField.PlaceDecomp.decomp E K w)] :
    ∃ Φ : NumberField.PlaceDecomp.decomp E K w ≃*
        ((w.adicCompletionIntegers K).decompositionSubgroup (FixedPoints.subfield (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K))),
      ∀ (σ : NumberField.PlaceDecomp.decomp E K w) (x : w.adicCompletion K),
        ((Φ σ : (w.adicCompletion K) ≃ₐ[FixedPoints.subfield (NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)] (w.adicCompletion K)) : _) x = σ • x := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_exists_mulEquiv_decompositionSubgroup_fixedPoints.solution
