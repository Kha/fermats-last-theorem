import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Theorems.Thm_AutomorphicForm_eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero
import P2M.Util
namespace P2MW.S_AutomorphicForm_eq_zero_of_isCuspAutomorphicFnAt_productionPinsOf_of_coversModCentre_of_forall_mem_eq_zero

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm AutomorphicForm.SiegelCovering

theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D U gen B).Z →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsCuspAutomorphicFnAt F (productionPinsOf F D U gen B) ξ φ)
    (W : Set (AdelicGL2 (𝓞 F) F)) (hcov : CoversModCentre F W)
    (h0 : ∀ x ∈ W, φ x = 0) : φ = 0 := by
  letI := (productionPinsOf F D U gen B).mS
  have h : IsLsXiFunction (𝓞 F) F (productionPinsOf F D U gen B).Z ξ φ :=
    ((lsXiMemberAt_iff (𝓞 F) F (productionPinsOf F D U gen B).μ (productionPinsOf F D U gen B).Z ξ
      (productionPinsOf F D U gen B).D φ).mp hφ.1).1
  exact AutomorphicForm.eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero F ξ φ h W hcov h0
