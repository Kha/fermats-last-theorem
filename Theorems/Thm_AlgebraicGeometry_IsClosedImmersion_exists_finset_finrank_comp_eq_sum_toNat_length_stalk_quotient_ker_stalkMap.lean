import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_exists_finset_finrank_comp_eq_sum_toNat_length_stalk_quotient_ker_stalkMap

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~finrank_eq_finsum_length_stalk_of_isFinite_of_isAlgClosed"

theorem AlgebraicGeometry.IsClosedImmersion.exists_finset_finrank_comp_eq_sum_toNat_length_stalk_quotient_ker_stalkMap
    (k : Type) [Field k] [IsAlgClosed k] {A K : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (κ : K ⟶ A) [IsClosedImmersion κ] [IsFinite (κ ≫ f)] :
    ∃ T : Finset K, (∀ y' : K, y' ∈ T) ∧ (∀ y' : K, IsClosed ({κ.base y'} : Set A)) ∧
      (((κ ≫ f).finrank (IsLocalRing.closedPoint k) : ℕ) : ℤ) =
        ∑ y' ∈ T, ((Module.length (A.presheaf.stalk (κ.base y'))
          ((A.presheaf.stalk (κ.base y')) ⧸ RingHom.ker (κ.stalkMap y').hom)).toNat : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_finset_finrank_comp_eq_sum_toNat_length_stalk_quotient_ker_stalkMap.solution
