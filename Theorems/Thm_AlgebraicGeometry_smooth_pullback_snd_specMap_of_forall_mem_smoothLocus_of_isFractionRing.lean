import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_smooth_pullback_snd_specMap_of_forall_mem_smoothLocus_of_isFractionRing

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.smooth_pullback_snd_specMap_of_forall_mem_smoothLocus_of_isFractionRing
    {A : Type u} [CommRing A] [IsDomain A] (L : Type u) [Field L] [Algebra A L] [IsFractionRing A L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFinitePresentation f]
    (hgen : ∀ x : X, (f.base x).asIdeal = ⊥ → x ∈ f.smoothLocus) :
    Smooth (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A L)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_smooth_pullback_snd_specMap_of_forall_mem_smoothLocus_of_isFractionRing.solution
