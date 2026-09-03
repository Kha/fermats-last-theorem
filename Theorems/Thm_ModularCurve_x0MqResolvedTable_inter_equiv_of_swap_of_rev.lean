import Mathlib
import Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixPicNeronCarriers
import Definitions.Def_ModularCurve_X0MqResolvedTable
import P2M.Util
import P2M.Sol.S_ModularCurve_x0MqResolvedTable_inter_equiv_of_swap_of_rev

set_option autoImplicit false

open ModularCurve MazurRapoportAppendix
open scoped BigOperators

theorem ModularCurve.x0MqResolvedTable_inter_equiv_of_swap_of_rev
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ)
    (Φ : X0MqComponents e ≃ X0MqComponents e)
    (hΦ0 : Φ (Sum.inl 0) = Sum.inl 1) (hΦ1 : Φ (Sum.inl 1) = Sum.inl 0)
    (hΦr : ∀ (x : ι) (k k' : Fin (e x - 1)), k.val + k'.val + 2 = e x → Φ (Sum.inr ⟨x, k⟩) = Sum.inr ⟨x, k'⟩)
    (a b : X0MqComponents e) :
    (x0MqResolvedTable e).inter (Φ a) (Φ b) = (x0MqResolvedTable e).inter a b := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_x0MqResolvedTable_inter_equiv_of_swap_of_rev.solution
