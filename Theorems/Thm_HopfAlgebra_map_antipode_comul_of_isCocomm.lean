import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_map_antipode_comul_of_isCocomm

open scoped TensorProduct in
theorem HopfAlgebra.map_antipode_comul_of_isCocomm {R : Type*} [CommSemiring R]
    {A : Type*} [Semiring A] [HopfAlgebra R A] (hcocomm : Coalgebra.IsCocomm R A) (a : A) :
    TensorProduct.map (HopfAlgebra.antipode R) (HopfAlgebra.antipode R) (Coalgebra.comul a)
      = Coalgebra.comul (HopfAlgebra.antipode R a) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_map_antipode_comul_of_isCocomm.solution
