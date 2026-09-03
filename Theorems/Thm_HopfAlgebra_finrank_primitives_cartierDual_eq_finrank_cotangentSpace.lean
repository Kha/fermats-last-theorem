import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_HopfAlgebra_finrank_primitives_cartierDual_eq_finrank_cotangentSpace

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

universe u v

theorem HopfAlgebra.finrank_primitives_cartierDual_eq_finrank_cotangentSpace
    (k : Type u) [Field k] (A : Type v) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A]
    [Module.Finite k A] :
    Module.finrank k ↥(primitives k (CartierDual k A)) = Module.finrank k (cotangentSpace k A) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_finrank_primitives_cartierDual_eq_finrank_cotangentSpace.solution
