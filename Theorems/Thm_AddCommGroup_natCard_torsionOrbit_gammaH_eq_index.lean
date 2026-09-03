import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_AddCommGroup_natCard_torsionOrbit_gammaH_eq_index

open scoped MatrixGroups

theorem AddCommGroup.natCard_torsionOrbit_gammaH_eq_index
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {A : Type*} [AddCommGroup A]
    (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ A M) :
    Nat.card {s : Set A // ∃ P : A, addOrderOf P = M ∧
        s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}} =
      (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_natCard_torsionOrbit_gammaH_eq_index.solution
