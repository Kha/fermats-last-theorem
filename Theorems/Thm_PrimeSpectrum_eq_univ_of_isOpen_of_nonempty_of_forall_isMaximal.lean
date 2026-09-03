import Mathlib
import P2M.Util
import P2M.Sol.S_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem PrimeSpectrum.eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal
    {A : Type u} [CommRing A] [IsJacobsonRing A]
    (U : Set (PrimeSpectrum A)) (hU : IsOpen U) (hne : U.Nonempty)
    (htrans : ∀ P Q : PrimeSpectrum A, P.asIdeal.IsMaximal → Q.asIdeal.IsMaximal → P ∈ U → Q ∈ U) :
    U = Set.univ := by p2m_exact_reverting @_root_.P2MW.S_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal.solution
