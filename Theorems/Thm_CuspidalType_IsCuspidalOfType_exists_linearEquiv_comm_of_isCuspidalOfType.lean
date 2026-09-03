import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_CuspidalType_IsCuspidalOfType_exists_linearEquiv_comm_of_isCuspidalOfType

set_option autoImplicit false

theorem CuspidalType.IsCuspidalOfType.exists_linearEquiv_comm_of_isCuspidalOfType
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {θ : (GaloisField q 2)ˣ →* Kˣ}
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {ρ : Representation K (CuspidalType.GL2 q) V}
    {V' : Type*} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] {ρ' : Representation K (CuspidalType.GL2 q) V'}
    (h : CuspidalType.IsCuspidalOfType θ ρ) (h' : CuspidalType.IsCuspidalOfType θ ρ') :
    ∃ e : V ≃ₗ[K] V', ∀ (g : CuspidalType.GL2 q) (v : V), e (ρ g v) = ρ' g (e v) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_IsCuspidalOfType_exists_linearEquiv_comm_of_isCuspidalOfType.solution
