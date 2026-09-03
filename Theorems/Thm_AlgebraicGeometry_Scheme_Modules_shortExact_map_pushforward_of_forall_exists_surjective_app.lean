import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_shortExact_map_pushforward_of_forall_exists_surjective_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

theorem AlgebraicGeometry.Scheme.Modules.shortExact_map_pushforward_of_forall_exists_surjective_app
    {X T : Scheme.{u}} (π : X ⟶ T) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hsurj : ∀ (U : T.Opens), ∀ y ∈ U, ∃ V : T.Opens, y ∈ V ∧ V ≤ U ∧
      Function.Surjective (S.g.app (π ⁻¹ᵁ V))) :
    (S.map (Scheme.Modules.pushforward π)).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_shortExact_map_pushforward_of_forall_exists_surjective_app.solution
