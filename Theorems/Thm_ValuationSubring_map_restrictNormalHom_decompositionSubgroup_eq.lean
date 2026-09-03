import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_map_restrictNormalHom_decompositionSubgroup_eq

set_option autoImplicit false

open scoped Pointwise

theorem ValuationSubring.map_restrictNormalHom_decompositionSubgroup_eq
    {E F : Type*} [Field E] [Field F] [Algebra E F] [IsGalois E F]
    (L : IntermediateField E F) [Normal E L] (A : ValuationSubring F) :
    (A.decompositionSubgroup E).map (AlgEquiv.restrictNormalHom L) =
      (A.comap (algebraMap L F)).decompositionSubgroup E := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_map_restrictNormalHom_decompositionSubgroup_eq.solution
