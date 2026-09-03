import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_existsUnique_forall_map_eq_of_forall_affineOpens

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.existsUnique_forall_map_eq_of_forall_affineOpens
    {X : Scheme.{u}} (M : X.Modules) (W : X.Opens)
    (s : ∀ U : X.affineOpens, (U : X.Opens) ≤ W → Γ(M, U))
    (hs : ∀ (U V : X.affineOpens) (hU : (U : X.Opens) ≤ W) (hVU : (V : X.Opens) ≤ U),
      M.presheaf.map (homOfLE hVU).op (s U hU) = s V (hVU.trans hU)) :
    ∃! t : Γ(M, W), ∀ (U : X.affineOpens) (hU : (U : X.Opens) ≤ W),
      M.presheaf.map (homOfLE hU).op t = s U hU := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_forall_map_eq_of_forall_affineOpens.solution
