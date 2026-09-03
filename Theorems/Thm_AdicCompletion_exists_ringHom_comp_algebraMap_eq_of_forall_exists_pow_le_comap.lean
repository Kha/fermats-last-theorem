import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap

set_option autoImplicit false
open Valued AdicCompletion in

theorem AdicCompletion.exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap
    {B : Type*} [CommRing B] (𝔪 : Ideal B) {S : Type*} [CommRing S] (J : Ideal S) [IsAdicComplete J S] (ev : B →+* S)
    (hcont : ∀ k : ℕ, ∃ n : ℕ, 𝔪 ^ n ≤ (J ^ k).comap ev) :
    ∃ ψ : AdicCompletion 𝔪 B →+* S, ψ.comp (algebraMap B (AdicCompletion 𝔪 B)) = ev := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap.solution
