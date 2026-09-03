import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_HeckeCharacter_exists_ne_zero_sub_one_mem_forall_pos_iff

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

theorem HeckeCharacter.exists_ne_zero_sub_one_mem_forall_pos_iff
    (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) (ε : (K →+* ℝ) → Prop) :
    ∃ β : 𝓞 K, β ≠ 0 ∧ β - 1 ∈ 𝔣 ∧ ∀ τ : K →+* ℝ, (0 < τ (β : K) ↔ ε τ) := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_exists_ne_zero_sub_one_mem_forall_pos_iff.solution
