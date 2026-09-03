import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_iSup_eq_top_isFrameOn

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u
theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isAffineOpen_iSup_eq_top_isFrameOn
    {X : Scheme.{u}} [CompactSpace ↥X] (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ (n : ℕ) (W : ULift.{u} (Fin n) → X.Opens),
      (∀ l, IsAffineOpen (W l)) ∧ (⨆ l, W l) = ⊤ ∧
      ∃ m : ∀ l, Γ(M, W l), ∀ l, Scheme.Modules.IsFrameOn (m l) (W l) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_iSup_eq_top_isFrameOn.solution
