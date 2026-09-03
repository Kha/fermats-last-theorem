import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_isFinite_of_etale

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_isFinite_of_etale
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsFinite f] [Etale f] (x : X) :
    ∃ U : X.Opens, (U : Set X) = {x} ∧ IsIso (U.ι ≫ f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_opens_coe_eq_singleton_and_isIso_iota_comp_of_isFinite_of_etale.solution
