import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_charZero_or_charP_of_algebra_ratLocalizedAt

open GaloisRep

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem GaloisRep.charZero_or_charP_of_algebra_ratLocalizedAt
    (ℓ : ℕ) [Fact ℓ.Prime] (K : Type*) [Field K] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) K] :
    CharZero K ∨ CharP K ℓ := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_charZero_or_charP_of_algebra_ratLocalizedAt.solution
