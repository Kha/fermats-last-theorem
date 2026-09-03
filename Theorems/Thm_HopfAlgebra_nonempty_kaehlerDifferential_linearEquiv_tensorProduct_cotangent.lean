import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers
import P2M.Util
import P2M.Sol.S_HopfAlgebra_nonempty_kaehlerDifferential_linearEquiv_tensorProduct_cotangent

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.nonempty_kaehlerDifferential_linearEquiv_tensorProduct_cotangent
    (R : Type) [CommRing R] (A : Type) [CommRing A] [HopfAlgebra R A] :
    Nonempty (Ω[A⁄R] ≃ₗ[A] A ⊗[R] (RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_nonempty_kaehlerDifferential_linearEquiv_tensorProduct_cotangent.solution
