import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

theorem AlgebraicGeometry.exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of R))
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] [IsSeparated g] [QuasiCompact g] :
    ∃ (Xf X' : Scheme.{u}) (i : Xf ⟶ X) (j : X' ⟶ X) (_ : IsOpenImmersion i)
      (_ : IsOpenImmersion j),
      IsFinite (i ≫ g) ∧
      Set.range i ∪ Set.range j = Set.univ ∧
      Disjoint (Set.range i) (Set.range j) ∧
      IsLocalRing.closedPoint R ∉ Set.range (j ≫ g) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing.solution
