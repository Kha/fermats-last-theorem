import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import P2M.Util
import P2M.Sol.S_Ihara_sl2_zmod_sq_congruence_preimage_commute

open scoped MatrixGroups
theorem Ihara.sl2_zmod_sq_congruence_preimage_commute (q : ℕ)
    {E : Type} [Group E] (π : E →* SL(2, ZMod (q ^ 2)))
    (hsurj : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hq : q.Prime) (hq5 : 5 ≤ q) :
    ∀ x, (∃ A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ 2)),
        ((π x : SL(2, ZMod (q ^ 2))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ 2)))
          = 1 + (q : ZMod (q ^ 2)) • A) →
    ∀ y, (∃ B : Matrix (Fin 2) (Fin 2) (ZMod (q ^ 2)),
        ((π y : SL(2, ZMod (q ^ 2))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ 2)))
          = 1 + (q : ZMod (q ^ 2)) • B) →
    Commute x y := by p2m_exact_reverting @_root_.P2MW.S_Ihara_sl2_zmod_sq_congruence_preimage_commute.solution
