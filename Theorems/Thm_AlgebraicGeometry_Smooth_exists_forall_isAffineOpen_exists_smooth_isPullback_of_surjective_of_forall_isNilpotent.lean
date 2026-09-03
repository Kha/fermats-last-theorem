import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_exists_forall_isAffineOpen_exists_smooth_isPullback_of_surjective_of_forall_isNilpotent

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Smooth.exists_forall_isAffineOpen_exists_smooth_isPullback_of_surjective_of_forall_isNilpotent
    {S S₀ : Type u} [CommRing S] [CommRing S₀] (p : S →+* S₀) (hp : Function.Surjective p)
    (hnil : ∀ x ∈ RingHom.ker p, IsNilpotent x)
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of S₀)) [Smooth f₀] (x : X₀) :
    ∃ U : X₀.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∀ V : X₀.Opens, IsAffineOpen V → V ≤ U →
        ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of S)) (g : (V : Scheme.{u}) ⟶ Y),
          IsAffine Y ∧ Smooth q ∧ IsPullback g (V.ι ≫ f₀) q (Spec.map (CommRingCat.ofHom p)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_exists_forall_isAffineOpen_exists_smooth_isPullback_of_surjective_of_forall_isNilpotent.solution
