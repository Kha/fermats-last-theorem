import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_formallyUnramified_of_forall_etale_pullback_snd

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.formallyUnramified_of_forall_etale_pullback_snd
    (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (φ : X ⟶ Y) (hφ : φ ≫ g = f)
    (het : ∀ (y : Spec (CommRingCat.of k) ⟶ Y), y ≫ g = 𝟙 _ → Etale (pullback.snd φ y)) :
    FormallyUnramified φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_formallyUnramified_of_forall_etale_pullback_snd.solution
