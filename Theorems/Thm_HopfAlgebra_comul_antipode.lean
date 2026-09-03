import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_comul_antipode

open scoped TensorProduct in
theorem HopfAlgebra.comul_antipode {R : Type*} [CommSemiring R]
    {A : Type*} [Semiring A] [HopfAlgebra R A] (a : A) :
    Coalgebra.comul (HopfAlgebra.antipode R a)
      = TensorProduct.comm R A A
          (TensorProduct.map (HopfAlgebra.antipode R) (HopfAlgebra.antipode R)
            (Coalgebra.comul a)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_comul_antipode.solution
