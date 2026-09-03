import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_IsCuspidalOfType_of_linearEquiv

set_option autoImplicit false

theorem CuspidalType.IsCuspidalOfType.of_linearEquiv {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {V' : Type*} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    {θ : (GaloisField q 2)ˣ →* Kˣ} {ρ : Representation K (GL2 q) V} {ρ' : Representation K (GL2 q) V'}
    (h : IsCuspidalOfType θ ρ) (e : V ≃ₗ[K] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    IsCuspidalOfType θ ρ' := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_IsCuspidalOfType_of_linearEquiv.solution
