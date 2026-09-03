import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isClosedMap_pullback_snd_of_directed_subalgebra

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isClosedMap_pullback_snd_of_directed_subalgebra
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type v} (S : ι → Subalgebra R A) (hdir : Directed (· ≤ ·) S) (hS : ∀ a : A, ∃ i, a ∈ S i)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f]
    (q : ∀ i, pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap R ↥(S i)))))
    (hq₁ : ∀ i, q i ≫ pullback.fst f _ = pullback.fst f _)
    (hq₂ : ∀ i, q i ≫ pullback.snd f _ =
      pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(S i) A)))
    (H : ∀ i, IsClosedMap (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R ↥(S i))))).base) :
    IsClosedMap (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).base := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isClosedMap_pullback_snd_of_directed_subalgebra.solution
