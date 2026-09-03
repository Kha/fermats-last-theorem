import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Etale.Field
import P2M.Util
import P2M.Sol.S_HopfAlgebra_algebra_etale_of_module_finite_of_charZero

theorem HopfAlgebra.algebra_etale_of_module_finite_of_charZero
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Module.Finite K A] :
    Algebra.Etale K A := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_algebra_etale_of_module_finite_of_charZero.solution
