import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_locallyOfFiniteType_and_quasiCompact_of_finite_openCover

universe u

open AlgebraicGeometry CategoryTheory

theorem solution
    {K : Type u} [CommRing K] {X J : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of K)} {σ : J ⟶ Spec (CommRingCat.of K)}
    [LocallyOfFiniteType f] [QuasiCompact f]
    {n : ℕ} (cov : Fin n → (X ⟶ J)) (hoi : ∀ i, IsOpenImmersion (cov i))
    (cov_over : ∀ i, cov i ≫ σ = f) (hcov : ⋃ i, Set.range (cov i).base = Set.univ) :
    LocallyOfFiniteType σ ∧ QuasiCompact σ := by
  constructor
  ·
    let 𝒰 : J.OpenCover := Scheme.Cover.mkOfCovers (Fin n) (fun _ ↦ X) cov
      (fun x ↦ by
        have hx : x ∈ ⋃ i, Set.range (cov i).base := hcov ▸ Set.mem_univ x
        simpa [Set.mem_iUnion, Set.mem_range] using hx)
      (fun j ↦ hoi j)
    exact IsZariskiLocalAtSource.of_openCover 𝒰 (fun i ↦ by
      show LocallyOfFiniteType (cov i ≫ σ)
      rw [cov_over i]; infer_instance)
  ·

    have hX : CompactSpace X :=
      HasAffineProperty.iff_of_isAffine (P := @QuasiCompact).mp ‹QuasiCompact f›
    have hJ : CompactSpace J := by
      constructor
      rw [← hcov]
      refine isCompact_iUnion (fun i ↦ ?_)
      rw [← Set.image_univ]
      exact (CompactSpace.isCompact_univ).image (cov i).continuous
    exact HasAffineProperty.iff_of_isAffine (P := @QuasiCompact).mpr hJ
