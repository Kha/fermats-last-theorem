import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_of_forall_nonempty_pullback_iso_of_isPullback_pi

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.nonempty_iso_of_forall_nonempty_pullback_iso_of_isPullback_pi
    {k : ℕ} (C : Fin k → Type u) [∀ i, CommRing (C i)]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of (∀ i, C i)))
    {Xi : Fin k → Scheme.{u}} (gi : ∀ i, Xi i ⟶ Spec (CommRingCat.of (C i))) (v : ∀ i, Xi i ⟶ X)
    (hv : ∀ i, IsPullback (v i) (gi i) g (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))))
    (M N : X.Modules)
    (h : ∀ i, Nonempty ((Scheme.Modules.pullback (v i)).obj M ≅ (Scheme.Modules.pullback (v i)).obj N)) :
    Nonempty (M ≅ N) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_of_forall_nonempty_pullback_iso_of_isPullback_pi.solution
