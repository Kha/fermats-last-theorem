import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_theta_scalarUnit_eq_one_of_isCuspidalOfType

set_option autoImplicit false

theorem CuspidalType.theta_scalarUnit_eq_one_of_isCuspidalOfType {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {θ : (GaloisField q 2)ˣ →* Kˣ} {ρ : Representation K (GL2 q) V}
    (h : IsCuspidalOfType θ ρ) (c : (ZMod q)ˣ) :
    θ (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = 1 := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_theta_scalarUnit_eq_one_of_isCuspidalOfType.solution
