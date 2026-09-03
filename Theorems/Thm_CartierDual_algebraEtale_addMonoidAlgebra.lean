import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_CartierDual_algebraEtale_addMonoidAlgebra

universe u v

theorem CartierDual.algebraEtale_addMonoidAlgebra
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Finite M] :
    Algebra.Etale R (CartierDual R (AddMonoidAlgebra R M)) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_algebraEtale_addMonoidAlgebra.solution
