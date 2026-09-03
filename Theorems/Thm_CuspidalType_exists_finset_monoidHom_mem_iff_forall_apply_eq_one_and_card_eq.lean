import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_exists_finset_monoidHom_mem_iff_forall_apply_eq_one_and_card_eq

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.exists_finset_monoidHom_mem_iff_forall_apply_eq_one_and_card_eq (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    ∃ S₀ : Finset ((GaloisField q 2)ˣ →* Kˣ),
      (∀ μ : (GaloisField q 2)ˣ →* Kˣ,
        μ ∈ S₀ ↔ ∀ c : (ZMod q)ˣ, μ (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = 1) ∧
      S₀.card = q + 1 := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_exists_finset_monoidHom_mem_iff_forall_apply_eq_one_and_card_eq.solution
