import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import P2M.Util
namespace P2MW.S_NumberField_PlaceDecomp_smul_algebraMap

set_option autoImplicit false
open scoped NumberField.PlaceDecomp

theorem solution (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (σ : NumberField.PlaceDecomp.decomp E K w) (x : K) :
    σ • algebraMap K (w.adicCompletion K) x = algebraMap K (w.adicCompletion K) ((σ : K ≃ₐ[E] K) x) := by
  rw [NumberField.PlaceDecomp.smul_def, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply, WithVal.equiv_symm_apply]
  rw [NumberField.PlaceDecomp.actRingEquiv_coe, WithVal.congr_apply]
  rfl
