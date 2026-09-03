import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_HopfAlgebra_isReduced_cartierDual_baseChange_addMonoidAlgebra

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.isReduced_cartierDual_baseChange_addMonoidAlgebra
    (R : Type) [CommRing R] (L : Type) [Field L] [Algebra R L]
    (Γ : Type) [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ] :
    IsReduced (CartierDual L (L ⊗[R] AddMonoidAlgebra R Γ)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_isReduced_cartierDual_baseChange_addMonoidAlgebra.solution
