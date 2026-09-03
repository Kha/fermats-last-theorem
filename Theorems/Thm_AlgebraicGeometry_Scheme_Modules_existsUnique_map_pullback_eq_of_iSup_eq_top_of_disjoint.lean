import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_existsUnique_map_pullback_eq_of_iSup_eq_top_of_disjoint

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.existsUnique_map_pullback_eq_of_iSup_eq_top_of_disjoint
    {Y : Scheme.{u}} {ι : Type v} (U : ι → Y.Opens) (hU : ⨆ i, U i = ⊤)
    (hdisj : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) (L₁ L₂ : Y.Modules)
    (φ : ∀ i, (Scheme.Modules.pullback (U i).ι).obj L₁ ⟶ (Scheme.Modules.pullback (U i).ι).obj L₂) :
    ∃! Φ : L₁ ⟶ L₂, ∀ i, (Scheme.Modules.pullback (U i).ι).map Φ = φ i := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_map_pullback_eq_of_iSup_eq_top_of_disjoint.solution
