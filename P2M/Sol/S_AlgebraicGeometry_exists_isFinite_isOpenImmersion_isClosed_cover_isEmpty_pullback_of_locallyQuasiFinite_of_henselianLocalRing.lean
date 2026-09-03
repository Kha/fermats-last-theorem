import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_exists_isFinite_isOpenImmersion_isClosed_cover_isEmpty_pullback_of_locallyQuasiFinite_of_henselianLocalRing

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of R))
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] [IsSeparated g] [QuasiCompact g] :
    ∃ (Xf X' : Scheme.{u}) (i : Xf ⟶ X) (j : X' ⟶ X) (_ : IsOpenImmersion i)
      (_ : IsOpenImmersion j),
      IsFinite (i ≫ g) ∧
      Set.range i ∪ Set.range j = Set.univ ∧
      Disjoint (Set.range i) (Set.range j) ∧
      IsLocalRing.closedPoint R ∉ Set.range (j ≫ g) ∧
      IsClosed (Set.range i) ∧
      IsEmpty ↑(pullback (j ≫ g)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) := by
  obtain ⟨Xf, X', i, j, hi, hj, hfin, hcov, hdisj, hnot⟩ :=
    AlgebraicGeometry.exists_isFinite_isOpenImmersion_disjoint_cover_of_locallyQuasiFinite_of_henselianLocalRing g
  refine ⟨Xf, X', i, j, hi, hj, hfin, hcov, hdisj, hnot, ?_, ?_⟩
  ·
    have hc : Set.range i = (Set.range j)ᶜ := by
      ext x
      refine ⟨fun hx hx' => Set.disjoint_left.mp hdisj hx hx', fun hx => ?_⟩
      exact ((hcov.symm ▸ Set.mem_univ x : x ∈ Set.range i ∪ Set.range j)).resolve_right hx
    rw [hc, isClosed_compl_iff]
    exact j.isOpenEmbedding.isOpen_range
  ·
    refine Scheme.isEmpty_pullback _ _ (Set.disjoint_left.mpr ?_)
    rintro _ ⟨y, rfl⟩ ⟨s, hs⟩
    refine hnot ⟨y, ?_⟩
    rw [← hs, Spec.map_apply, CommRingCat.hom_ofHom, IsLocalRing.PrimeSpectrum.comap_residue]
