import Mathlib
import Theorems.Thm_AlgebraicGeometry_isClosedImmersion_of_universallyClosed_of_universallyInjective_of_formallyUnramified
import Theorems.Thm_AlgebraicGeometry_formallyUnramified_of_forall_geometricFibre_formallyUnramified
import Theorems.Thm_AlgebraicGeometry_universallyInjective_of_forall_geometricFibre_universallyInjective
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isClosedImmersion_of_isProper_of_forall_geometricFibre_isClosedImmersion

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {S : Type u} [CommRing S] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of S)) [IsProper p]
    (q : Y ⟶ Spec (CommRingCat.of S)) [IsSeparated q]
    (φ : X ⟶ Y) (hφ : φ ≫ q = p)
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
      ∃ (X' Y' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k)) (q' : Y' ⟶ Spec (CommRingCat.of k))
        (φ' : X' ⟶ Y') (iX : X' ⟶ X) (iY : Y' ⟶ Y),
        IsPullback iX p' p (Spec.map (CommRingCat.ofHom sk)) ∧
        IsPullback iY q' q (Spec.map (CommRingCat.ofHom sk)) ∧
        φ' ≫ q' = p' ∧ iX ≫ φ = φ' ≫ iY ∧ IsClosedImmersion φ') :
    IsClosedImmersion φ := by
  have hα1 : FormallyUnramified φ :=
    AlgebraicGeometry.formallyUnramified_of_forall_geometricFibre_formallyUnramified p q φ hφ fun k _ _ sk => by
      obtain ⟨X', Y', p', q', φ', iX, iY, h1, h2, h3, h4, h5⟩ := hfib k sk
      exact ⟨X', Y', p', q', φ', iX, iY, h1, h2, h3, h4, inferInstance⟩
  have hα2 : UniversallyInjective φ :=
    AlgebraicGeometry.universallyInjective_of_forall_geometricFibre_universallyInjective p q φ hφ fun k _ _ sk => by
      obtain ⟨X', Y', p', q', φ', iX, iY, h1, h2, h3, h4, h5⟩ := hfib k sk
      exact ⟨X', Y', p', q', φ', iX, iY, h1, h2, h3, h4, inferInstance⟩
  have : UniversallyClosed (φ ≫ q) := by rw [hφ]; infer_instance
  have hUC : UniversallyClosed φ := .of_comp_of_isSeparated φ q
  have : LocallyOfFiniteType (φ ≫ q) := by rw [hφ]; infer_instance
  have hLFT : LocallyOfFiniteType φ := locallyOfFiniteType_of_comp φ q
  exact AlgebraicGeometry.isClosedImmersion_of_universallyClosed_of_universallyInjective_of_formallyUnramified φ
