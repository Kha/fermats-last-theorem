import Mathlib
import Definitions.Def_AlgebraicGeometry_ResolvedModelGlueComponents
import P2M.Util
import P2M.Sol.S_V3Glue_ChartInput_comap_iotaY_compG_chainPosPrime_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem V3Glue.ChartInput.comap_iotaY_compG_chainPosPrime_eq {X : Scheme.{0}} {N : Type} (C : V3Glue.ChartInput X N)
    (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
    (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
    (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0) (n : N)
    (F : Fin (C.thick n + 1) → (C.Res n).IdealSheafData)

    (hFexc : ∀ k : Fin (C.thick n - 1), F ⟨(k : ℕ) + 1, by omega⟩ =
      Scheme.IdealSheafData.vanishingIdeal ⟨closure {gRes n k}, isClosed_closure⟩)
    (hred : ∀ k : Fin (C.thick n - 1), IsReduced (pullback (C.g n) (F ⟨(k : ℕ) + 1, by omega⟩).subschemeι))

    (hU : ∀ j : Fin 2, ξ j ∈ C.U n) (lam : Fin 2 → C.Res n)
    (hFend : ∀ j : Fin 2, ((F (Fin.cases 0 (fun _ => Fin.last _) j)).support : Set (C.Res n)) = closure {lam j})
    (hredEnd : ∀ j : Fin 2, IsReduced (pullback (C.g n) (F (Fin.cases 0 (fun _ => Fin.last _) j)).subschemeι))
    (hlam : ∀ j : Fin 2, (C.g n).base ⁻¹' {lam j} = {C.ξY ξ hξ n j (hU j)}) (d : Fin (C.thick n + 1)) :
    (C.compG hRF gRes hgRes ξ hξ (C.chainPos' n d)).comap (C.toGlueInput.ιY n) = (F d).comap (C.g n) := by p2m_exact_reverting @_root_.P2MW.S_V3Glue_ChartInput_comap_iotaY_compG_chainPosPrime_eq.solution
