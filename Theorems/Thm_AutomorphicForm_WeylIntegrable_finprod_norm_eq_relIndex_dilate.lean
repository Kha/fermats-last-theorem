import Definitions.Def_AutomorphicForm_WeylSelectors
import P2M.Util
import P2M.Sol.S_AutomorphicForm_WeylIntegrable_finprod_norm_eq_relIndex_dilate
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec

set_option autoImplicit false

theorem AutomorphicForm.WeylIntegrable.finprod_norm_eq_relIndex_dilate (F : Type) [Field F] [NumberField F]
    (y : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ)
    (hy : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      1 ≤ Valued.v ((y : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) v)) :
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
        ‖(y : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) v‖
      = ((intLattice F).relIndex (dilate F y) : ℝ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_WeylIntegrable_finprod_norm_eq_relIndex_dilate.solution
