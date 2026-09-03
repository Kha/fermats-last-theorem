import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

open scoped Classical in

theorem AutomorphicForm.exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt
    (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (_hv : v ∈ S)
    (k : AdelicGL2 (𝓞 F) F) (_hk : k ∈ maximalCompactAt F S) :
    ∃ k' kv : AdelicGL2 (𝓞 F) F,
      k' ∈ maximalCompactAt F (S.erase v) ∧
      kv ∈ maximalCompactAt F {v} ∧ glArch (𝓞 F) F kv = 1 ∧
      k = k' * kv ∧ k' * kv = kv * k' := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt.solution
