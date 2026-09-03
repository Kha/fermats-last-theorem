import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isOpen_setOf_forall_preimage_mem_of_universallyClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isOpen_setOf_forall_preimage_mem_of_universallyClosed
    {Z T Y : Scheme.{u}} (π : Z ⟶ T) [UniversallyClosed π] (φ : Z ⟶ Y) (V : Y.Opens) :
    IsOpen {t : T | ∀ z : Z, π.base z = t → φ.base z ∈ V} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isOpen_setOf_forall_preimage_mem_of_universallyClosed.solution
