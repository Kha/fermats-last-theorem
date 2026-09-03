import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_pow_add_one_eq_one_iff_forall_theta_scalarUnit_eq_one

set_option autoImplicit false

theorem CuspidalType.pow_add_one_eq_one_iff_forall_theta_scalarUnit_eq_one {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    (θ : (GaloisField q 2)ˣ →* Kˣ) :
    θ ^ (q + 1) = 1 ↔
      ∀ c : (ZMod q)ˣ, θ (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = 1 := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_pow_add_one_eq_one_iff_forall_theta_scalarUnit_eq_one.solution
