import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isFinite_of_finite_setOf_exists_section_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f]
    (hfin : {x : X | ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint k) = x}.Finite) :
    IsFinite f := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hsub : closedPoints X ⊆
      {x : X | ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint k) = x} :=
    fun x hx => ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx,
      pointOfClosedPoint_apply f x hx _⟩
  have : DiscreteTopology X := JacobsonSpace.discreteTopology (hfin.subset hsub)
  have : Finite X :=
    Set.finite_univ_iff.mp (closedPoints_eq_univ (X := X) ▸ hfin.subset hsub)
  have hqf : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_finite_preimage_singleton f fun _ => Set.toFinite _
  have hq : RingHom.QuasiFinite (f.appTop).hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyQuasiFinite)).mp hqf
  refine (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mpr ⟨inferInstance, ?_⟩
  have : IsArtinianRing Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.isArtinianRing
  algebraize [(f.appTop).hom]
  exact Module.Finite.of_quasiFinite
