import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType t] (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t, z.left.base (IsLocalRing.closedPoint k) = x := by
  refine ⟨Over.homMk (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x) ?_, ?_⟩
  · change (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x) ≫ t = 𝟙 _
    rw [Category.assoc, ← SpecMap_residueFieldIsoBase_inv t x hx, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id]
  · change (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x).base
        (IsLocalRing.closedPoint k) = x
    have hmem : (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x).base
        (IsLocalRing.closedPoint k) ∈ Set.range (X.fromSpecResidueField x).base :=
      ⟨(Spec.map (residueFieldIsoBase t x hx).hom).base (IsLocalRing.closedPoint k), rfl⟩
    rw [Scheme.range_fromSpecResidueField] at hmem
    exact hmem
