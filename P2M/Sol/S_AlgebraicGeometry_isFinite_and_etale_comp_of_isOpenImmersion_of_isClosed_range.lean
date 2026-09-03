import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isFinite_and_etale_comp_of_isOpenImmersion_of_isClosed_range

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ClopenPieceFiniteEtaleSol

lemma isFinite_of_isOpenImmersion_of_isClosed_range {V U : Scheme.{u}} (i : V ⟶ U) [IsOpenImmersion i]
    (hi : IsClosed (Set.range i.base)) : IsFinite i :=
  have : IsClosedImmersion i := IsClosedImmersion.of_isPreimmersion i hi
  inferInstance

end ClopenPieceFiniteEtaleSol

open ClopenPieceFiniteEtaleSol in
theorem solution
    {V U X : Scheme.{u}} (i : V ⟶ U) [IsOpenImmersion i] (hi : IsClosed (Set.range i.base))
    (π : U ⟶ X) [IsFinite π] [AlgebraicGeometry.Etale π] :
    IsFinite (i ≫ π) ∧ AlgebraicGeometry.Etale (i ≫ π) :=
  have : IsFinite i := isFinite_of_isOpenImmersion_of_isClosed_range i hi
  ⟨inferInstance, inferInstance⟩
