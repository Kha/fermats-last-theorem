import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_TateModule_nonempty_basis_of_card_torsionBy
set_option autoImplicit false

theorem TateModule.nonempty_basis_of_card_torsionBy (p : ℕ) [Fact p.Prime] {M : Type} [AddCommGroup M] (r : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r) :
    Nonempty (Module.Basis (Fin r) ℤ_[p] (TateModule p M)) := by p2m_exact_reverting @_root_.P2MW.S_TateModule_nonempty_basis_of_card_torsionBy.solution
