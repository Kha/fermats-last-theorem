import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_range_subset_of_closedPoint_mem

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_range_subset_of_closedPoint_mem.AlgebraicGeometry"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Hom Spec Scheme" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom Opens" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "continuous" end AlgebraicGeometry.Scheme.Hom
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in
theorem AlgebraicGeometry.Scheme.Hom.range_subset_of_closedPoint_mem_aux {O : Type u} [CommRing O] [IsLocalRing O] {Y : Scheme.{u}}
    (W : Y.Opens) (σ : Spec (CommRingCat.of O) ⟶ Y) (hW : σ.base (IsLocalRing.closedPoint O) ∈ W) :
    Set.range σ.base ⊆ (W : Set Y) := by
  rintro _ ⟨x, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint x).map σ.continuous).mem_open W.2 hW

theorem solution
    {O : Type u} [CommRing O] [IsLocalRing O] {Y : Scheme.{u}}
    (W : Y.Opens) (σ : Spec (CommRingCat.of O) ⟶ Y) (hW : σ.base (IsLocalRing.closedPoint O) ∈ W) :
    Set.range σ.base ⊆ (W : Set Y) :=
  AlgebraicGeometry.Scheme.Hom.range_subset_of_closedPoint_mem_aux W σ hW
