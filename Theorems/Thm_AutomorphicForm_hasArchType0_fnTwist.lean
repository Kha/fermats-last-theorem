import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_FnTwist
import P2M.Util
import P2M.Sol.S_AutomorphicForm_hasArchType0_fnTwist

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.hasArchType0_fnTwist
    (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : HasArchType₀ F χ φ) :
    HasArchType₀ F χ (fnTwist F η φ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_hasArchType0_fnTwist.solution
