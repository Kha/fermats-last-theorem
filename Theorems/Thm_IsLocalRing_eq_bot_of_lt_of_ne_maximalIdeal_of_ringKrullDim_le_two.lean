import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two

set_option autoImplicit false

universe u v
open IsLocalRing in

theorem IsLocalRing.eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two
    {B : Type u} [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B]
    {R : Type v} [CommRing R] (e : AdicCompletion (maximalIdeal B) B ≃+* R) (hR : ringKrullDim R ≤ 2) :
    ∀ 𝔭 𝔮 : Ideal B, 𝔭.IsPrime → 𝔮.IsPrime → 𝔮 ≠ maximalIdeal B → 𝔭 < 𝔮 → 𝔭 = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two.solution
