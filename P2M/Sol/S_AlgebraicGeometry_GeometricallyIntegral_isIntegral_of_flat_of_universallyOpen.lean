import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "GeometricallyReduced GeometricallyIntegral GeometricallyIntegral.isIntegral_of_isLocallyNoetherian GeometricallyIrreducible IsIntegral GeometricallyIrreducible.irreducibleSpace Scheme UniversallyOpen isIntegral_iff_irreducibleSpace_and_isReduced Flat GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents"
p2m_open "AlgebraicGeometry"

theorem finite_irreducibleComponents_of_irreducibleSpace (S : Type*) [TopologicalSpace S]
    [IrreducibleSpace S] : (irreducibleComponents S).Finite := by
  refine (Set.finite_singleton (Set.univ : Set S)).subset ?_
  intro Z hZ
  rw [Set.mem_singleton_iff]
  exact hZ.eq_of_le (IrreducibleSpace.isIrreducible_univ S) (Set.subset_univ Z)

end AlgebraicGeometry

theorem solution
    {X S : Scheme.{u}} (f : X ⟶ S) [GeometricallyIntegral f] [Flat f] [UniversallyOpen f]
    [IsIntegral S] : IsIntegral X := by
  have : Finite (irreducibleComponents S) :=
    (AlgebraicGeometry.finite_irreducibleComponents_of_irreducibleSpace S).to_subtype
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  exact ⟨GeometricallyIrreducible.irreducibleSpace f f.isOpenMap,
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents f⟩
