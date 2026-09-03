import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_IsSeparated_of_isClosedImmersion_mapDesc_openCover

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsZariskiLocalAtTarget Scheme Scheme.Pullback.openCoverOfLeftRight Scheme.OpenCover IsClosedImmersion IsSeparated IsZariskiLocalAtTarget.of_openCover"
p2m_open "AlgebraicGeometry"

universe u

p2m_open_scoped "AlgebraicGeometry.IsSeparated" in

theorem IsSeparated.of_isClosedImmersion_mapDesc_openCover_proof
    {N S : Scheme.{u}} (g : N ⟶ S) (𝒰 : Scheme.OpenCover.{u} N)
    (h : ∀ i j : 𝒰.I₀, IsClosedImmersion (pullback.mapDesc (𝒰.f i) (𝒰.f j) g)) :
    IsSeparated g := by
  constructor
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 g g) fun ij => ?_
  obtain ⟨i, j⟩ := ij
  have hsq := pullback_map_diagonal_isPullback (𝒰.f i) (𝒰.f j) g
  change IsClosedImmersion (pullback.snd (pullback.diagonal g)
    (pullback.map (𝒰.f i ≫ g) (𝒰.f j ≫ g) g g (𝒰.f i) (𝒰.f j) (𝟙 _) (Category.comp_id _) (Category.comp_id _)))
  have key : hsq.isoPullback.inv ≫ pullback.mapDesc (𝒰.f i) (𝒰.f j) g = pullback.snd (pullback.diagonal g)
      (pullback.map (𝒰.f i ≫ g) (𝒰.f j ≫ g) g g (𝒰.f i) (𝒰.f j) (𝟙 _) (Category.comp_id _) (Category.comp_id _)) := by
    rw [Iso.inv_comp_eq]
    exact hsq.isoPullback_hom_snd.symm
  rw [← key]
  haveI := h i j
  infer_instance

end AlgebraicGeometry

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_IsSeparated_of_isClosedImmersion_mapDesc_openCover.AlgebraicGeometry"

universe u

theorem solution
    {N S : Scheme.{u}} (g : N ⟶ S) (𝒰 : Scheme.OpenCover.{u} N)
    (h : ∀ i j : 𝒰.I₀, IsClosedImmersion (pullback.mapDesc (𝒰.f i) (𝒰.f j) g)) :
    IsSeparated g :=
  AlgebraicGeometry.IsSeparated.of_isClosedImmersion_mapDesc_openCover_proof g 𝒰 h
