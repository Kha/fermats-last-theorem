import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central

set_option autoImplicit false

open CuspidalType

theorem CuspidalType.exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K (GL2 q) V)
    (hirr : ∀ W : Subrepresentation ρ, W.toSubmodule ≠ ⊥ → W.toSubmodule = ⊤)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0)
    (hcent : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id) :
    ∃ θ : (GaloisField q 2)ˣ →* Kˣ, IsCuspidalOfType θ ρ := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central.solution
