import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_formallyUnramified_of_forall_geometricFibre_formallyUnramified

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.formallyUnramified_of_forall_geometricFibre_formallyUnramified
    {S : Type u} [CommRing S] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of S)) [LocallyOfFiniteType p]
    (q : Y ⟶ Spec (CommRingCat.of S))
    (φ : X ⟶ Y) (hφ : φ ≫ q = p)
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
      ∃ (X' Y' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k)) (q' : Y' ⟶ Spec (CommRingCat.of k))
        (φ' : X' ⟶ Y') (iX : X' ⟶ X) (iY : Y' ⟶ Y),
        IsPullback iX p' p (Spec.map (CommRingCat.ofHom sk)) ∧
        IsPullback iY q' q (Spec.map (CommRingCat.ofHom sk)) ∧
        φ' ≫ q' = p' ∧ iX ≫ φ = φ' ≫ iY ∧ FormallyUnramified φ') :
    FormallyUnramified φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_formallyUnramified_of_forall_geometricFibre_formallyUnramified.solution
