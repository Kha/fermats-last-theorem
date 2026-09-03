import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isClosedImmersion_pullbackLift_of_isClosedImmersion_pullbackLift_of_isPullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isClosedImmersion_pullbackLift_of_isClosedImmersion_pullbackLift_of_isPullback
    {G S : Scheme.{u}} (g : G ⟶ S)
    {R k L A : Type u} [CommRing R] [CommRing k] [CommRing L] [CommRing A] [Algebra R k] [Algebra R L]
    (sR : Spec (CommRingCat.of R) ⟶ S)

    (ι : Spec (CommRingCat.of L) ⟶ G)
    (h1 : ι ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ sR)
    (hcl : IsClosedImmersion (pullback.lift (f := g) (g := sR) ι (Spec.map (CommRingCat.ofHom (algebraMap R L))) h1))

    (s : Spec (CommRingCat.of k) ⟶ S) (hs : s = Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ sR)
    (a : L →+* A) (c : k →+* A)
    (hA : IsPullback (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom c))
      (Spec.map (CommRingCat.ofHom (algebraMap R L))) (Spec.map (CommRingCat.ofHom (algebraMap R k))))
    (hsq : (Spec.map (CommRingCat.ofHom a) ≫ ι) ≫ g = Spec.map (CommRingCat.ofHom c) ≫ s) :
    IsClosedImmersion (pullback.lift (f := g) (g := s) (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isClosedImmersion_pullbackLift_of_isClosedImmersion_pullbackLift_of_isPullback.solution
