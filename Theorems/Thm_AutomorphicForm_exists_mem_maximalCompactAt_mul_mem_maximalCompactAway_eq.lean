import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq
    (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (k : AdelicGL2 (𝓞 F) F) (_hk : k ∈ adelicMaximalCompact F) :
    ∃ k₁ k₂ : AdelicGL2 (𝓞 F) F, k₁ ∈ maximalCompactAt F S ∧ k₂ ∈ maximalCompactAway F S ∧ k = k₁ * k₂ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq.solution
