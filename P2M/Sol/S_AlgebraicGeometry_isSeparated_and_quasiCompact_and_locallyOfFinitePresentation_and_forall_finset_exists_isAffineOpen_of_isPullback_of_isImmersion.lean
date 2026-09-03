import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isImmersion_proj
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isSeparated_and_quasiCompact_and_locallyOfFinitePresentation_and_forall_finset_exists_isAffineOpen_of_isPullback_of_isImmersion

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {R : Type} [CommRing R] [IsNoetherianRing R] {M : ℕ} {H : Scheme.{0}}
    (j : H ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (M + 1)) R))
    [IsImmersion j] [LocallyOfFiniteType j] [QuasiCompact j]
    (𝒪 : Type) [CommRing 𝒪] [Algebra R 𝒪]
    {H' : Scheme.{0}} (π' : H' ⟶ Spec (CommRingCat.of 𝒪)) (g : H' ⟶ H)
    (hg : IsPullback g π' (j ≫ ProjSpace.π R M) (Spec.map (CommRingCat.ofHom (algebraMap R 𝒪)))) :
    IsSeparated π' ∧ QuasiCompact π' ∧ LocallyOfFinitePresentation π' ∧
      (∀ F : Finset H', ∃ V : H'.Opens, IsAffineOpen V ∧ ∀ x ∈ F, x ∈ V) := by
  have hsep : IsSeparated (j ≫ ProjSpace.π R M) := inferInstance
  have hqc : QuasiCompact (j ≫ ProjSpace.π R M) := inferInstance
  have hft : LocallyOfFiniteType (j ≫ ProjSpace.π R M) := inferInstance
  have hlfp : LocallyOfFinitePresentation (j ≫ ProjSpace.π R M) := inferInstance
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsSeparated) hg hsep
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hg hqc
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hg hlfp
  · intro F
    have hsq := ProjSpace.isPullback_map R 𝒪 M
    have w : (g ≫ j) ≫ ProjSpace.π R M = π' ≫ Spec.map (CommRingCat.ofHom (algebraMap R 𝒪)) := by
      simpa only [Category.assoc] using hg.w
    let j' : H' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (M + 1)) 𝒪) := hsq.lift (g ≫ j) π' w
    have hj₁ : j' ≫ ProjSpace.map R 𝒪 M = g ≫ j := hsq.lift_fst _ _ w
    have hj₂ : j' ≫ ProjSpace.π 𝒪 M = π' := hsq.lift_snd _ _ w
    have big : IsPullback g (j' ≫ ProjSpace.π 𝒪 M) (j ≫ ProjSpace.π R M)
        (Spec.map (CommRingCat.ofHom (algebraMap R 𝒪))) := by
      rw [hj₂]; exact hg
    have top : IsPullback g j' j (ProjSpace.map R 𝒪 M) := IsPullback.of_bot big (by rw [hj₁]) hsq
    haveI : IsImmersion j' := MorphismProperty.of_isPullback (P := @IsImmersion) top inferInstance
    exact AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isImmersion_proj _ j' F
