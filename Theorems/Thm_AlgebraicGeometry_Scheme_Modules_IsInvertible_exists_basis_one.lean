import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_basis_one

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_basis_one
    {X : Scheme.{u}} {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) (x : X) :
    ∃ (V : X.Opens), x ∈ V ∧ ∃ u : Γ(L, V), ∀ (W : X.Opens) (hW : W ≤ V),
      ∃ b : Module.Basis (Fin 1) Γ(X, W) Γ(L, W), b 0 = L.presheaf.map (homOfLE hW).op u := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_basis_one.solution
