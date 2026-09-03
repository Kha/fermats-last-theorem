import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_frame_of_frame_pullback
    {X X' : Scheme.{u}} (p : X' ⟶ X) (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (m : Γ(M, ⊤)) (z : X')
    (h : ∃ U' : X'.Opens, z ∈ U' ∧ ∀ V' : X'.Opens, V' ≤ U' →
      Function.Bijective fun g : Γ(X', V') =>
        g • (((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤) m) :
            Γ((Scheme.Modules.pullback p).obj M, V'))) :
    ∃ U : X.Opens, p z ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op m : Γ(M, V)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback.solution
