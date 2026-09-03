import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_shortExact_of_app_injective_of_locallySurjective_of_locallyExact

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

theorem AlgebraicGeometry.Scheme.Modules.shortExact_of_app_injective_of_locallySurjective_of_locallyExact
    {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hf : ∀ U : X.Opens, Function.Injective (S.f.app U))
    (hg : ∀ (U : X.Opens) (s : Γ(S.X₃, U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ S.X₃.presheaf.map (homOfLE i).op s ∈ Set.range (S.g.app V))
    (hfg : ∀ (U : X.Opens) (m : Γ(S.X₂, U)), S.g.app U m = 0 → ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ S.X₂.presheaf.map (homOfLE i).op m ∈ Set.range (S.f.app V)) :
    S.ShortExact := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_shortExact_of_app_injective_of_locallySurjective_of_locallyExact.solution
