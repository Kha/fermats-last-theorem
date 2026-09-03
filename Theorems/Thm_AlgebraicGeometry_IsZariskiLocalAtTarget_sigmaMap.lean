import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.IsZariskiLocalAtTarget.sigmaMap
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {σ : Type u} {X Y : σ → Scheme.{u}} (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, P (f i)) :
    P (Limits.Sigma.map f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap.solution
