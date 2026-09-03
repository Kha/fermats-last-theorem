import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIso_of_smooth_of_subsingleton_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_smooth_of_subsingleton_of_isAlgClosed
    (k : Type) [Field k] [IsAlgClosed k] {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of k)) [Smooth g]
    (s : Spec (CommRingCat.of k) ⟶ G) (hs : s ≫ g = 𝟙 _)
    (huniq : ∀ s' : Spec (CommRingCat.of k) ⟶ G, s' ≫ g = 𝟙 _ → s' = s) :
    IsIso g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_of_smooth_of_subsingleton_of_isAlgClosed.solution
