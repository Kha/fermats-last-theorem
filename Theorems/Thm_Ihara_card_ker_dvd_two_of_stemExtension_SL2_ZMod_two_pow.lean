import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Commutator.Basic
import P2M.Util
import P2M.Sol.S_Ihara_card_ker_dvd_two_of_stemExtension_SL2_ZMod_two_pow

open scoped MatrixGroups

theorem Ihara.card_ker_dvd_two_of_stemExtension_SL2_ZMod_two_pow {a : ℕ} (E : Type) [Group E]
    (π : E →* SL(2, ZMod (2 ^ a))) (hπ : Function.Surjective π)
    (hcen : MonoidHom.ker π ≤ Subgroup.center E) (hcomm : MonoidHom.ker π ≤ commutator E) :
    Nat.card (MonoidHom.ker π) ∣ 2 := by p2m_exact_reverting @_root_.P2MW.S_Ihara_card_ker_dvd_two_of_stemExtension_SL2_ZMod_two_pow.solution
