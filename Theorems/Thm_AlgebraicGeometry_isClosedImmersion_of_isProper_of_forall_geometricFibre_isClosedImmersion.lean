import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isClosedImmersion_of_isProper_of_forall_geometricFibre_isClosedImmersion

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~isClosedImmersion_of_universallyClosed_of_universallyInjective_of_formallyUnramified"

theorem AlgebraicGeometry.isClosedImmersion_of_isProper_of_forall_geometricFibre_isClosedImmersion
    {S : Type u} [CommRing S] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of S)) [IsProper p]
    (q : Y ⟶ Spec (CommRingCat.of S)) [IsSeparated q]
    (φ : X ⟶ Y) (hφ : φ ≫ q = p)
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
      ∃ (X' Y' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k)) (q' : Y' ⟶ Spec (CommRingCat.of k))
        (φ' : X' ⟶ Y') (iX : X' ⟶ X) (iY : Y' ⟶ Y),
        IsPullback iX p' p (Spec.map (CommRingCat.ofHom sk)) ∧
        IsPullback iY q' q (Spec.map (CommRingCat.ofHom sk)) ∧
        φ' ≫ q' = p' ∧ iX ≫ φ = φ' ≫ iY ∧ IsClosedImmersion φ') :
    IsClosedImmersion φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isClosedImmersion_of_isProper_of_forall_geometricFibre_isClosedImmersion.solution
