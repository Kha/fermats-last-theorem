import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_HopfAlgebra_isReduced_cartierDual_of_isReduced_cartierDual_baseChange

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.isReduced_cartierDual_of_isReduced_cartierDual_baseChange
    (K : Type) [Field K] (A : Type) [CommRing A] [HopfAlgebra K A] [Coalgebra.IsCocomm K A]
    [Module.Finite K A] [Module.Free K A]
    (L : Type) [Field L] [Algebra K L]
    (hL : IsReduced (CartierDual L (L ⊗[K] A))) :
    IsReduced (CartierDual K A) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_isReduced_cartierDual_of_isReduced_cartierDual_baseChange.solution
