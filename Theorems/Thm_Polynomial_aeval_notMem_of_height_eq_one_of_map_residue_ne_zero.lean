import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_aeval_notMem_of_height_eq_one_of_map_residue_ne_zero

set_option autoImplicit false

theorem Polynomial.aeval_notMem_of_height_eq_one_of_map_residue_ne_zero
    {A C : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing C] [IsDomain C] [Algebra A C]
    (x : C) (hx : Function.Injective (Polynomial.aeval (R := A) x))
    (hint : (Polynomial.aeval (R := A) x).toRingHom.IsIntegral)
    (Q : Ideal C) [Q.IsPrime] (hQ : Q.height = 1)
    (hQm : (IsLocalRing.maximalIdeal A).map (algebraMap A C) ≤ Q)
    (P : Polynomial A) (hP : P.map (IsLocalRing.residue A) ≠ 0) :
    Polynomial.aeval x P ∉ Q := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_aeval_notMem_of_height_eq_one_of_map_residue_ne_zero.solution
