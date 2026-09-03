import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import P2M.Util
import P2M.Sol.S_AdelicDock_finEmbed_localEmbed_mem_levelOne_inf_finiteAdelicGL2Subgroup

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm LocalGL2 NumberField.AdelicLevel

theorem AdelicDock.finEmbed_localEmbed_mem_levelOne_inf_finiteAdelicGL2Subgroup
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)) :
    finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v k) ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by p2m_exact_reverting @_root_.P2MW.S_AdelicDock_finEmbed_localEmbed_mem_levelOne_inf_finiteAdelicGL2Subgroup.solution
