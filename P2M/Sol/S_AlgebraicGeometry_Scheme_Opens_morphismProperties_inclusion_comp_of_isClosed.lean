import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Opens_morphismProperties_inclusion_comp_of_isClosed

set_option autoImplicit false

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Opens_morphismProperties_inclusion_comp_of_isClosed.AlgebraicGeometry CategoryTheory"

universe u

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension Scheme.Opens.range_ι QuasiCompact LocallyOfFiniteType Spec Scheme Flat IsSeparated Scheme.Opens" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Opens.range_ι Opens" namespace Opens p2m_export "AlgebraicGeometry.Scheme.Opens" "range_ι ι" end AlgebraicGeometry.Scheme.Opens
namespace AlgebraicGeometry.Scheme.Opens
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

private theorem _root_.AlgebraicGeometry.Scheme.Opens.quasiCompact_ι_of_isClosed {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClosed (U : Set X)) : QuasiCompact U.ι := by
  constructor
  intro V _ hV
  rw [U.ι.isOpenEmbedding.isInducing.isCompact_iff, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
  exact hV.inter_right hU

end AlgebraicGeometry.Scheme.Opens
p2m_export "" "AlgebraicGeometry.Scheme.Opens.quasiCompact_ι_of_isClosed"
theorem solution
    {B : Type u} [CommRing B] {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of B))
    (U : X.Opens) (hU : IsClosed (U : Set X)) :
    (IsSeparated πX → IsSeparated (U.ι ≫ πX)) ∧ (QuasiCompact πX → QuasiCompact (U.ι ≫ πX)) ∧
      (LocallyOfFiniteType πX → LocallyOfFiniteType (U.ι ≫ πX)) ∧ (Flat πX → Flat (U.ι ≫ πX)) ∧
      (SmoothOfRelativeDimension 1 πX → SmoothOfRelativeDimension 1 (U.ι ≫ πX)) := by
  haveI : QuasiCompact U.ι := U.quasiCompact_ι_of_isClosed hU
  refine ⟨fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance, fun _ => ?_⟩
  exact inferInstanceAs <| SmoothOfRelativeDimension (0 + 1) (U.ι ≫ πX)
