import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Finite_quotient_of_isUnit_leadingCoeff_of_mem

set_option autoImplicit false

open Polynomial

universe u v

theorem Module.Finite.quotient_of_isUnit_leadingCoeff_of_mem
    (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A] [Algebra R[X] A]
    [IsScalarTower R R[X] A] [Module.Finite R[X] A]
    (N : R[X]) (hN : IsUnit N.leadingCoeff) (I : Ideal A) (hNI : algebraMap R[X] A N ∈ I) :
    Module.Finite R (A ⧸ I) := by p2m_exact_reverting @_root_.P2MW.S_Module_Finite_quotient_of_isUnit_leadingCoeff_of_mem.solution
