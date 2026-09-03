import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_etale_pullback_snd_of_forall_dualNumber_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.etale_pullback_snd_of_forall_dualNumber_comp_eq
    (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (φ : X ⟶ Y) (hφ : φ ≫ g = f)
    (hinj : ∀ P Q : Spec (CommRingCat.of (DualNumber k)) ⟶ X,
      P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) →
      Q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) →
      P ≫ φ = Q ≫ φ → P = Q)
    (y : Spec (CommRingCat.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    Etale (pullback.snd φ y) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_etale_pullback_snd_of_forall_dualNumber_comp_eq.solution
