import Mathlib
import P2M.Util
import P2M.Sol.S_AlgEquiv_isOpen_ker_restrictNormalHom

theorem AlgEquiv.isOpen_ker_restrictNormalHom (K L : Type*) [Field K] [Field L] [Algebra K L]
    (E : Type*) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L] [Normal K E]
    [FiniteDimensional K E] :
    IsOpen ((AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker : Set (L ≃ₐ[K] L)) := by p2m_exact_reverting @_root_.P2MW.S_AlgEquiv_isOpen_ker_restrictNormalHom.solution
