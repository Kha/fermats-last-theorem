import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_NumberField_stabilizer_primitiveRoot_three_le_of_forall_inertia_inf_le
set_option autoImplicit false
open scoped NumberField
theorem NumberField.stabilizer_primitiveRoot_three_le_of_forall_inertia_inf_le
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (H : Subgroup (L ≃ₐ[ℚ] L))
    (hH : ∀ P : Ideal (NumberField.RingOfIntegers L), P.IsMaximal →
      P.inertia (L ≃ₐ[ℚ] L) ⊓ MulAction.stabilizer (L ≃ₐ[ℚ] L) ζ ≤ H) :
    MulAction.stabilizer (L ≃ₐ[ℚ] L) ζ ≤ H := by p2m_exact_reverting @_root_.P2MW.S_NumberField_stabilizer_primitiveRoot_three_le_of_forall_inertia_inf_le.solution
