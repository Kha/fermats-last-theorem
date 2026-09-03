import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat_hasDerivAt_comp_sub_smul

set_option autoImplicit false

open NumberField NumberField.AdelicHaar MeasureTheory
open AutomorphicForm IsDedekindDomain NumberField.TateGlobal

theorem NumberField.AdelicFourier.exists_mem_schwartzBruhat_hasDerivAt_comp_sub_smul
    (F : Type) [Field F] [NumberField F]
    {B : AdeleRing (𝓞 F) F → ℂ} (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (e : mixedEmbedding.mixedSpace F) :
    ∃ B' : AdeleRing (𝓞 F) F → ℂ, B' ∈ NumberField.AdelicFourier.schwartzBruhat F ∧
      ∀ (x : AdeleRing (𝓞 F) F) (t : ℝ),
        HasDerivAt (fun s : ℝ => B (x - @id (AdeleRing (𝓞 F) F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (s • e), 0)))
          (B' (x - @id (AdeleRing (𝓞 F) F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • e), 0))) t := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_exists_mem_schwartzBruhat_hasDerivAt_comp_sub_smul.solution
