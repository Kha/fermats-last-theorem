import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_pullback_locally_mem_span_unit

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullback_locally_mem_span_unit
    {X Y : Scheme.{u}} (ψ : X ⟶ Y) (E : Y.Modules) {W : X.Opens}
    (y : Γ((Scheme.Modules.pullback ψ).obj E, W)) {x : X} (hx : x ∈ W)
    {U₀ : Y.Opens} (hU₀ : ψ.base x ∈ U₀) :
    ∃ (U : Y.Opens) (W' : X.Opens) (i : W' ≤ W) (j : W' ≤ ψ ⁻¹ᵁ U), U ≤ U₀ ∧ x ∈ W' ∧
      ((Scheme.Modules.pullback ψ).obj E).presheaf.map (homOfLE i).op y ∈
        Submodule.span Γ(X, W') (Set.range fun e : Γ(E, U) =>
          ((Scheme.Modules.pullback ψ).obj E).presheaf.map (homOfLE j).op
            ((((Scheme.Modules.pullbackPushforwardAdjunction ψ).unit.app E).app U e :
              Γ((Scheme.Modules.pullback ψ).obj E, ψ ⁻¹ᵁ U)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_locally_mem_span_unit.solution
