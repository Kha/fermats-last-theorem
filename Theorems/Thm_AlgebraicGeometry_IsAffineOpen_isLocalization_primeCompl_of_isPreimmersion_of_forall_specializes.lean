import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsAffineOpen_isLocalization_primeCompl_of_isPreimmersion_of_forall_specializes

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsAffineOpen.isLocalization_primeCompl_of_isPreimmersion_of_forall_specializes
    {X : Scheme.{u}} [IsReduced X] {V : X.Opens} (hV : IsAffineOpen V)
    (x : X) (hxV : x ∈ V) (hmax : ∀ y : X, y ⤳ x → y = x)
    (F : Type u) [Field F] (φ : Spec (CommRingCat.of F) ⟶ X) [IsPreimmersion φ]
    (hφx : φ.base (IsLocalRing.closedPoint F) = x)
    [Algebra Γ(X, V) F]
    (hφ : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) F)) ≫ hV.fromSpec = φ) :
    IsLocalization (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsAffineOpen_isLocalization_primeCompl_of_isPreimmersion_of_forall_specializes.solution
