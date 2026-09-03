import Definitions.Def_CohCarrier_Lower
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeT_apply_eq_sumEquiv

set_option autoImplicit false
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem CohCarrier.heckeT_apply_eq_sumEquiv (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    {V : Type} [AddCommGroup V] {ι : Type*} [Fintype ι]
    (e : ι ≃ Quotient (QuotientGroup.rightRel (GammaHUpper M H ℓ)))
    (F : Additive ↥(GammaH M H) →+ V) (γ : ↥(GammaH M H)) :
    heckeT M H ℓ V F (Additive.ofMul γ)
      = ∑ i : ι, F (Additive.ofMul (conjL M H ℓ (slip (GammaHUpper M H ℓ) (e i) γ))) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeT_apply_eq_sumEquiv.solution
