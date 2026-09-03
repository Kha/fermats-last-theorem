import Mathlib
import Definitions.Def_AlgebraicGeometry_ResolvedModelGlueComponents
import P2M.Util
import P2M.Sol.S_V3Glue_ChartInput_exists_eq_etaG_of_ringKrullDim_le_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem V3Glue.ChartInput.exists_eq_etaG_of_ringKrullDim_le_one {X : Scheme.{0}} {N : Type} (C : V3Glue.ChartInput X N)
    (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
    (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
    (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)
    (hq : ∀ n (y : C.Y n), ((C.q n).base y).1 ∈ C.X0 → y ∈ Set.range (C.j n).base)
    (V : C.B.Opens)
    (hX0max : ∀ z : X, z ∈ C.X0 → C.πX.base z ∉ V → ringKrullDim (X.presheaf.stalk z) ≤ 1 → z = ξ 0 ∨ z = ξ 1)
    (hExcMax : ∀ (n : N) (yn : C.Y n), ((C.q n).base yn).1 = C.x n → ringKrullDim ((C.Y n).presheaf.stalk yn) ≤ 1 →
      ∃ k, (C.toGlueInput.ιY n).base yn = C.ηG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩))
    (y : C.toGlueInput.glued) (hy : (C.toGlueInput.toDR ≫ C.πX).base y ∉ V)
    (h1 : ringKrullDim (C.toGlueInput.glued.presheaf.stalk y) ≤ 1) :
    ∃ v, y = C.ηG hRF gRes hgRes ξ hξ v := by p2m_exact_reverting @_root_.P2MW.S_V3Glue_ChartInput_exists_eq_etaG_of_ringKrullDim_le_one.solution
