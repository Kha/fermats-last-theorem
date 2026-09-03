import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_TateModule_sub_one_pow_rep_eq_zero_of_pow_sub_one_pow_eq_zero_of_forall_torsionBy_smul_eq

set_option autoImplicit false

theorem TateModule.sub_one_pow_rep_eq_zero_of_pow_sub_one_pow_eq_zero_of_forall_torsionBy_smul_eq
    {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M] {G : Type} [Monoid G] [DistribMulAction G M]
    (g : G) {a : ℕ} (ha : 3 ≤ p ^ a)
    (hfix : ∀ x ∈ Submodule.torsionBy ℤ M ((p ^ a : ℕ) : ℤ), g • x = x)
    {m : ℕ} (hm : 0 < m) {n : ℕ}
    (hn : ((TateModule.rep p M G g) ^ m - 1) ^ n = 0) :
    (TateModule.rep p M G g - 1) ^ n = 0 := by p2m_exact_reverting @_root_.P2MW.S_TateModule_sub_one_pow_rep_eq_zero_of_pow_sub_one_pow_eq_zero_of_forall_torsionBy_smul_eq.solution
