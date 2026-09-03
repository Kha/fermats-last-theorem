import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isCuspidalFn_integral_maximalCompactAtHaar_mul_of_isCuspidalFn

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.isCuspidalFn_integral_maximalCompactAtHaar_mul_of_isCuspidalFn
    (K : Type) [Field K] [NumberField K]
    (ν : @Measure (AdeleRing (𝓞 K) K) (adeleBorel (𝓞 K) K)) (hν : ν Set.univ ≠ ⊤)
    (B : Set (AdeleRing (𝓞 K) K)) (hB : IsCompact B) (hνB : ν Bᶜ = 0)
    (κ : ↥(maximalCompactAt K ∅) → ℝ) (hκc : Continuous κ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f)
    (hfc : @IsCuspidalFn (AdeleRing (𝓞 K) K) (adeleBorel (𝓞 K) K) (AdelicGL2 (𝓞 K) K) _ ν
      (fun q => unipotentGL2 q) f) :
    @IsCuspidalFn (AdeleRing (𝓞 K) K) (adeleBorel (𝓞 K) K) (AdelicGL2 (𝓞 K) K) _ ν
      (fun q => unipotentGL2 q) (fun x => ∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactAtHaar K ∅)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isCuspidalFn_integral_maximalCompactAtHaar_mul_of_isCuspidalFn.solution
