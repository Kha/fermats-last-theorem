import Mathlib
import Theorems.Thm_AlgebraicGeometry_formallyUnramified_of_forall_dualNumber_comp_eq
import Theorems.Thm_AlgebraicGeometry_mono_of_formallyUnramified_of_forall_comp_eq
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isClosedImmersion_of_isProper_of_forall_dualNumber_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (g : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated g] [LocallyOfFiniteType g]
    (φ : X ⟶ Y) (hφ : φ ≫ g = f)
    (hinj : ∀ P Q : Spec (CommRingCat.of (DualNumber k)) ⟶ X,
      P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) →
      Q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) →
      P ≫ φ = Q ≫ φ → P = Q) :
    IsClosedImmersion φ := by

  have hcomp : IsProper (φ ≫ g) := by rw [hφ]; infer_instance
  have hprop : IsProper φ := IsProper.of_comp φ g
  have : LocallyOfFiniteType f := inferInstance

  have hunr : FormallyUnramified φ :=
    AlgebraicGeometry.formallyUnramified_of_forall_dualNumber_comp_eq k f g φ hφ hinj

  have hpts : ∀ P Q : Spec (CommRingCat.of k) ⟶ X, P ≫ f = 𝟙 _ → Q ≫ f = 𝟙 _ → P ≫ φ = Q ≫ φ → P = Q := by
    intro P Q hP hQ hPQ
    let π : Spec (CommRingCat.of (DualNumber k)) ⟶ Spec (CommRingCat.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
    let σ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DualNumber k)) :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)
    have hσπ : σ ≫ π = 𝟙 _ := by
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
    have h := hinj (π ≫ P) (π ≫ Q) (by rw [Category.assoc, hP, Category.comp_id])
      (by rw [Category.assoc, hQ, Category.comp_id]) (by rw [Category.assoc, Category.assoc, hPQ])
    have := congrArg (fun t => σ ≫ t) h
    simpa only [← Category.assoc, hσπ, Category.id_comp] using this
  have hmono : Mono φ := AlgebraicGeometry.mono_of_formallyUnramified_of_forall_comp_eq k f g φ hφ hpts
  exact (IsClosedImmersion.iff_isProper_and_mono φ).mpr ⟨hprop, hmono⟩
