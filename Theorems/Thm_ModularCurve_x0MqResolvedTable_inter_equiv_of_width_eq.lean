import Mathlib
import Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixPicNeronCarriers
import Definitions.Def_ModularCurve_X0MqResolvedTable
import P2M.Util
import P2M.Sol.S_ModularCurve_x0MqResolvedTable_inter_equiv_of_width_eq

set_option autoImplicit false

open ModularCurve MazurRapoportAppendix
open scoped BigOperators

theorem ModularCurve.x0MqResolvedTable_inter_equiv_of_width_eq
    {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (e : ι → ℕ) (e' : ι' → ℕ) (φ : ι ≃ ι') (hφ : ∀ x, e' (φ x) = e x)
    (Φ : X0MqComponents e ≃ X0MqComponents e')
    (hΦl : ∀ i : Fin 2, Φ (Sum.inl i) = Sum.inl i)
    (hΦr : ∀ (x : ι) (k : Fin (e x - 1)) (k' : Fin (e' (φ x) - 1)), k.val = k'.val →
      Φ (Sum.inr ⟨x, k⟩) = Sum.inr ⟨φ x, k'⟩)
    (a b : X0MqComponents e) :
    (x0MqResolvedTable e').inter (Φ a) (Φ b) = (x0MqResolvedTable e).inter a b := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_x0MqResolvedTable_inter_equiv_of_width_eq.solution
