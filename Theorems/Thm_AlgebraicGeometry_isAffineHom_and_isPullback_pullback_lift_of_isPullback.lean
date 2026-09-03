import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isAffineHom_and_isPullback_pullback_lift_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isAffineHom_and_isPullback_pullback_lift_of_isPullback
    {T k : Type u} [CommRing T] [CommRing k] (ρ : T →+* k)
    {A₀ Ak : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (fk : Ak ⟶ Spec (CommRingCat.of k))
    (i₀ : Ak ⟶ A₀) [IsAffineHom i₀] (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ))) :
    IsAffineHom (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
          (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ∧
    IsPullback (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀)
          (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition]))
      (pullback.fst fk fk ≫ fk) (pullback.fst f₀ f₀ ≫ f₀) (Spec.map (CommRingCat.ofHom ρ)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isAffineHom_and_isPullback_pullback_lift_of_isPullback.solution
