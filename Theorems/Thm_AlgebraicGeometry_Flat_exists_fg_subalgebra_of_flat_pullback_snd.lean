import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Flat_exists_fg_subalgebra_of_flat_pullback_snd

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Flat.exists_fg_subalgebra_of_flat_pullback_snd
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f] [LocallyOfFinitePresentation f]
    [Flat (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))] (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      Flat (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Flat_exists_fg_subalgebra_of_flat_pullback_snd.solution
