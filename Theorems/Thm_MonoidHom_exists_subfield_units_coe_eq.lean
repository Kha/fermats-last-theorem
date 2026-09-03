import Mathlib
import P2M.Util
import P2M.Sol.S_MonoidHom_exists_subfield_units_coe_eq

set_option autoImplicit false

theorem MonoidHom.exists_subfield_units_coe_eq
    {G : Type*} [Group G] {L : Type*} [Field L] (K : Subfield L)
    (F : G →* G →* Lˣ) (hF : ∀ α β : G, ((F α β : Lˣ) : L) ∈ K) :
    ∃ F' : G →* G →* (↥K)ˣ, ∀ α β : G, (((F' α β : (↥K)ˣ) : ↥K) : L) = F α β := by p2m_exact_reverting @_root_.P2MW.S_MonoidHom_exists_subfield_units_coe_eq.solution
