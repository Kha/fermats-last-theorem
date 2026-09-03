import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isSmoothCuspAutomorphicFnAt_twistedCentralChar_fnTwist_productionPinsOf

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm

theorem AutomorphicForm.isSmoothCuspAutomorphicFnAt_twistedCentralChar_fnTwist_productionPinsOf
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D U gen B).Z →* ℂˣ)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hη : HeckeCharacter.IsFiniteOrderHeckeChar F η)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsSmoothCuspAutomorphicFnAt F (productionPinsOf F D U gen B) ξ φ) :
    IsSmoothCuspAutomorphicFnAt F (productionPinsOf F D U gen B) (twistedCentralChar F _ ξ η) (fnTwist F η φ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isSmoothCuspAutomorphicFnAt_twistedCentralChar_fnTwist_productionPinsOf.solution
