import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_existsUnique_comp_eq_of_universallyClosed_of_closedPoint_notMem_range

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

theorem AlgebraicGeometry.existsUnique_comp_eq_of_universallyClosed_of_closedPoint_notMem_range
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X Xf X' T : Scheme.{u}} (g : X ⟶ Spec (.of R))
    (i : Xf ⟶ X) [IsOpenImmersion i] (j : X' ⟶ X)
    (hcover : Set.range i ∪ Set.range j = Set.univ)
    (hempty : IsLocalRing.closedPoint R ∉ Set.range (j ≫ g))
    (f : T ⟶ X) [UniversallyClosed (f ≫ g)] :
    ∃! f' : T ⟶ Xf, f' ≫ i = f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_existsUnique_comp_eq_of_universallyClosed_of_closedPoint_notMem_range.solution
