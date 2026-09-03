import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_IsCuspidalOfType_toSubmodule_eq_top_of_ne_bot

set_option autoImplicit false

theorem CuspidalType.IsCuspidalOfType.toSubmodule_eq_top_of_ne_bot {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {θ : (GaloisField q 2)ˣ →* Kˣ} {ρ : Representation K (GL2 q) V} (h : IsCuspidalOfType θ ρ)
    (hq : (q : K) ≠ 0) (hq1 : ((q : K) - 1 ≠ 0)) (W : Subrepresentation ρ) (hW : W.toSubmodule ≠ ⊥) :
    W.toSubmodule = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_IsCuspidalOfType_toSubmodule_eq_top_of_ne_bot.solution
