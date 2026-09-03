import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_finiteFlat_tensorProduct

open scoped TensorProduct
theorem HopfAlgebra.finiteFlat_tensorProduct {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [HopfAlgebra R A] [HopfAlgebra R B]
    [Module.Finite R A] [Module.Flat R A] [Module.Finite R B] [Module.Flat R B] :
    Module.Finite R (A ⊗[R] B) ∧ Module.Flat R (A ⊗[R] B) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_finiteFlat_tensorProduct.solution
