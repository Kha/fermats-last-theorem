import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace FD0625672e

open scoped TensorProduct

theorem ringKrullDim_quotient_map_maximalIdeal_eq_zero
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra.QuasiFinite R S] :
    ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) = 0 := by

  let e : (maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ (maximalIdeal R).map (algebraMap R S) :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).symm.restrictScalars R)

  haveI : IsArtinianRing ((maximalIdeal R).Fiber S) := inferInstance
  haveI hA : IsArtinianRing (S ⧸ (maximalIdeal R).map (algebraMap R S)) := e.surjective.isArtinianRing
  haveI : Ring.KrullDimLE 0 (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mp hA).2

  haveI : Nontrivial (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
    rw [Ideal.Quotient.nontrivial_iff]
    exact ((((local_hom_TFAE (algebraMap R S)).out 0 2 rfl rfl).mp inferInstance).trans_lt
      (inferInstance : (maximalIdeal S).IsMaximal).ne_top.lt_top).ne
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

end FD0625672e

theorem solution
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [IsLocallyNoetherian Y] (x : X) :
    ringKrullDim ((X.presheaf.stalk x) ⧸
      (maximalIdeal (Y.presheaf.stalk (g.base x))).map (g.stalkMap x).hom) = 0 := by
  letI : Algebra (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x) := (g.stalkMap x).hom.toAlgebra
  haveI : Algebra.QuasiFinite (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x) := g.quasiFiniteAt x
  haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (g.stalkMap x).hom)
  exact FD0625672e.ringKrullDim_quotient_map_maximalIdeal_eq_zero (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x)

#print axioms solution
