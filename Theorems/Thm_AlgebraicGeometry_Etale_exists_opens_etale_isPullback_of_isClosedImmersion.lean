import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Etale_exists_opens_etale_isPullback_of_isClosedImmersion

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Etale.exists_opens_etale_isPullback_of_isClosedImmersion
    {X X₀ Y₀ : Scheme.{0}} (i : X₀ ⟶ X) [IsClosedImmersion i] (q₀ : Y₀ ⟶ X₀) [Etale q₀] (y : Y₀) :
    ∃ (V₀ : Y₀.Opens) (_ : y ∈ V₀) (V : Scheme.{0}) (qV : V ⟶ X) (_ : Etale qV) (jV : (V₀ : Scheme.{0}) ⟶ V),
      IsPullback jV (V₀.ι ≫ q₀) qV i := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Etale_exists_opens_etale_isPullback_of_isClosedImmersion.solution
