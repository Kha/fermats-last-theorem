import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_existsUnique_germToFunctionField_eq_of_iSup_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

theorem AlgebraicGeometry.Scheme.existsUnique_germToFunctionField_eq_of_iSup_eq
    {X : Scheme.{u}} [IsIntegral X] {ι : Type u} (V : ι → X.Opens) (W : X.Opens) (hV : iSup V = W)
    [hW : Nonempty W] [hVi : ∀ i, Nonempty (V i)]
    (f : X.functionField) (s : ∀ i, Γ(X, V i)) (hs : ∀ i, X.germToFunctionField (V i) (s i) = f) :
    ∃! t : Γ(X, W), X.germToFunctionField W t = f ∧
      ∀ i, X.presheaf.map (homOfLE (hV ▸ le_iSup V i : V i ≤ W)).op t = s i := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_existsUnique_germToFunctionField_eq_of_iSup_eq.solution
