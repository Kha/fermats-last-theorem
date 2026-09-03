import Mathlib
import Definitions.Def_AlgebraicGeometry_ResolvedModelGlueComponents
import P2M.Util
import P2M.Sol.S_V3Glue_ChartInput_prod_compG_comap_iotaY_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem V3Glue.ChartInput.prod_compG_comap_iotaY_eq {X : Scheme.{0}} {N : Type} [Fintype N] (C : V3Glue.ChartInput X N)
    (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
    (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
    (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0) (n : N) (ϖ : Γ(C.B, ⊤))
    (F : C.Comps → (C.Res n).IdealSheafData)
    (hF : ∀ v, (C.compG hRF gRes hgRes ξ hξ v).comap (C.toGlueInput.ιY n) = (F v).comap (C.g n))
    (hprod : ∏ v, F v = (Scheme.IdealSheafData.ofIdealTop (Ideal.span {ϖ})).comap (C.ρ n ≫ C.σ n)) :
    (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap (C.toGlueInput.ιY n) =
      (Scheme.IdealSheafData.ofIdealTop (Ideal.span {ϖ})).comap (C.toB n) := by p2m_exact_reverting @_root_.P2MW.S_V3Glue_ChartInput_prod_compG_comap_iotaY_eq.solution
