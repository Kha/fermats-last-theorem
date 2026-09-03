import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_pullback_map_app_eq_smul_of_forall_app_eq_smul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullback_map_app_eq_smul_of_forall_app_eq_smul
    {T X : Scheme.{u}} (g : T ⟶ X) (L : X.Modules) (u : Γ(X, ⊤)) (γ : L ⟶ L)
    (hγ : ∀ (U : X.Opens) (s : Γ(L, U)), γ.app U s = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op u • s)
    (V : T.Opens) (t : Γ((Scheme.Modules.pullback g).obj L, V)) :
    ((Scheme.Modules.pullback g).map γ).app V t = T.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (g.appTop u) • t := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_map_app_eq_smul_of_forall_app_eq_smul.solution
