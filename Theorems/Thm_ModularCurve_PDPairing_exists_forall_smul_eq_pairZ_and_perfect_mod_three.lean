import Definitions.Def_ModularCurve_PDPairing
import P2M.Util
import P2M.Sol.S_ModularCurve_PDPairing_exists_forall_smul_eq_pairZ_and_perfect_mod_three

set_option autoImplicit false

open CongruenceSubgroup

theorem ModularCurve.PDPairing.exists_forall_smul_eq_pairZ_and_perfect_mod_three [IsFreeGroup ↥(Gamma 4)] :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ (M : ℕ) [NeZero M],
      ∃ B : ModularCurve.Period.parabolicHoms ℤ (Gamma0 M) ℤ →ₗ[ℤ]
          ModularCurve.Period.parabolicHoms ℤ (Gamma0 M) ℤ →ₗ[ℤ] ℤ,
        c • B = ModularCurve.PDPairing.pairZ M ∧
          (∀ x, (∀ y, (3 : ℤ) ∣ B x y) → ∃ x', x = (3 : ℤ) • x') ∧
          (∀ y, (∀ x, (3 : ℤ) ∣ B x y) → ∃ y', y = (3 : ℤ) • y') := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PDPairing_exists_forall_smul_eq_pairZ_and_perfect_mod_three.solution
