import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_rankAtStalk_sections_eq_one_of_locallyTrivial

universe u

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

theorem AlgebraicGeometry.Scheme.Modules.rankAtStalk_sections_eq_one_of_locallyTrivial
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.affineOpens) (𝔭 : PrimeSpectrum Γ(X, U.1)) :
    Module.rankAtStalk (R := Γ(X, U.1)) Γ(M, U.1) 𝔭 = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_rankAtStalk_sections_eq_one_of_locallyTrivial.solution
