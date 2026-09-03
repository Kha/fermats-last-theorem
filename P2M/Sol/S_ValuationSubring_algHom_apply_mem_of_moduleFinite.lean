import Mathlib
import P2M.Util
namespace P2MW.S_ValuationSubring_algHom_apply_mem_of_moduleFinite

set_option autoImplicit false

theorem solution
    {R : Type} [CommRing R] {L : Type} [Field L] [Algebra R L]
    (A : ValuationSubring L) (hR : ∀ r : R, algebraMap R L r ∈ A)
    {H : Type} [CommRing H] [Algebra R H] [Module.Finite R H]
    (f : H →ₐ[R] L) (h : H) : f h ∈ A := by

  letI : Algebra R A := ((algebraMap R L).codRestrict A.toSubring hR).toAlgebra
  haveI : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have hint : IsIntegral R (f h) := (Algebra.IsIntegral.isIntegral (R := R) h).map f
  have hintA : IsIntegral A (f h) := hint.tower_top

  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintA
  rw [← ha]
  exact a.2
