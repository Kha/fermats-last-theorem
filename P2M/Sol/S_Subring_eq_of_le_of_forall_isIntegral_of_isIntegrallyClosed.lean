import Mathlib
import P2M.Util
namespace P2MW.S_Subring_eq_of_le_of_forall_isIntegral_of_isIntegrallyClosed

set_option autoImplicit false

theorem solution
    {F : Type*} [Field F] (Bflat B : Subring F) (hle : Bflat ≤ B)
    [IsFractionRing ↥Bflat F] [IsIntegrallyClosed ↥Bflat]
    (hint : ∀ b ∈ B, IsIntegral ↥Bflat b) :
    B = Bflat := by
  refine le_antisymm (fun b hb => ?_) hle
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥Bflat) (K := F)).mp (hint b hb)
  rw [← hy]
  exact y.2
