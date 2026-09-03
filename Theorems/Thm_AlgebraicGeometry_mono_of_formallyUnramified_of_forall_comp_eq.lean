import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_mono_of_formallyUnramified_of_forall_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.mono_of_formallyUnramified_of_forall_comp_eq
    (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (φ : X ⟶ Y) (hφ : φ ≫ g = f) [FormallyUnramified φ]
    (hinj : ∀ P Q : Spec (CommRingCat.of k) ⟶ X, P ≫ f = 𝟙 _ → Q ≫ f = 𝟙 _ → P ≫ φ = Q ≫ φ → P = Q) :
    Mono φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_mono_of_formallyUnramified_of_forall_comp_eq.solution
