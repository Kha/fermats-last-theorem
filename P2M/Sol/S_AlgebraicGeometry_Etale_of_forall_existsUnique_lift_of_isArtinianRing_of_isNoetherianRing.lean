import Mathlib
import Theorems.Thm_AlgebraicGeometry_Smooth_of_forall_exists_lift_of_isArtinianRing_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_formallyUnramified_of_forall_lift_unique_of_isArtinianRing
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Etale_of_forall_existsUnique_lift_of_isArtinianRing_of_isNoetherianRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem solution
    {R : Type} [CommRing R] [IsNoetherianRing R] {M : Scheme.{0}} (ϖ : M ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation ϖ]
    (h : ∀ (T' T : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
      [CommRing T] [Nontrivial T] (p : T' →+* T), Function.Surjective p → RingHom.ker p * maximalIdeal T' = ⊥ →
      ∀ (s : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of R)) (m : Spec (CommRingCat.of T) ⟶ M),
        m ≫ ϖ = Spec.map (CommRingCat.ofHom p) ≫ s →
        ∃! m' : Spec (CommRingCat.of T') ⟶ M, m' ≫ ϖ = s ∧ Spec.map (CommRingCat.ofHom p) ≫ m' = m) :
    Etale ϖ := by
  haveI : LocallyOfFiniteType ϖ := inferInstance
  have hS : Smooth ϖ :=
    AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_isNoetherianRing ϖ
      (fun T' T _ _ _ _ _ _ p hp hsmall s m hm => (h T' T p hp hsmall s m hm).exists)
  have hU : FormallyUnramified ϖ :=
    AlgebraicGeometry.formallyUnramified_of_forall_lift_unique_of_isArtinianRing ϖ
      (fun T' T _ _ _ _ _ _ p hp hsmall s m hm m₁ m₂ h₁ h₁' h₂ h₂' =>
        (h T' T p hp hsmall s m hm).unique ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩)
  haveI := hS
  haveI := hU
  haveI : Flat ϖ := inferInstance
  exact Etale.of_formallyUnramified_of_flat ϖ
