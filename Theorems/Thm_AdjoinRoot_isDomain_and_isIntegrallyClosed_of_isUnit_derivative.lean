import Mathlib
import P2M.Util
import P2M.Sol.S_AdjoinRoot_isDomain_and_isIntegrallyClosed_of_isUnit_derivative

set_option autoImplicit false

universe u

open Polynomial in

theorem AdjoinRoot.isDomain_and_isIntegrallyClosed_of_isUnit_derivative
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (f : R[X]) (hfm : f.Monic) (hfi : Irreducible f)
    (hu : IsUnit (AdjoinRoot.mk f (derivative f))) :
    IsDomain (AdjoinRoot f) ∧ IsIntegrallyClosed (AdjoinRoot f) := by p2m_exact_reverting @_root_.P2MW.S_AdjoinRoot_isDomain_and_isIntegrallyClosed_of_isUnit_derivative.solution
