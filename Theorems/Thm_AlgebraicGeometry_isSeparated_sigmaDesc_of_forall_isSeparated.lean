import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isSeparated_sigmaDesc_of_forall_isSeparated
    {σ : Type u} (X : σ → Scheme.{u}) {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y)
    (hf : ∀ i, IsSeparated (f i)) : IsSeparated (Sigma.desc f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated.solution
