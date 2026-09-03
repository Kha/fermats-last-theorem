import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isUnit_and_mul_act_eq_add_and_prod_iterate_act_eq_norm_mul_of_mem_adelicBorel_of_diagonal

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.isUnit_and_mul_act_eq_add_and_prod_iterate_act_eq_norm_mul_of_mem_adelicBorel_of_diagonal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (t : GL (Fin 2) L) (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (b : AdelicGL2 (𝓞 L) L) (hb : b ∈ AutomorphicForm.adelicBorel (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ)
    (A B E : AdeleRing (𝓞 L) L)
    (hA : ((b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) : AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 = A)
    (hB : ((b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) : AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 = B)
    (hE : ((b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) : AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = E) :
    (IsUnit A ∧ IsUnit B) ∧
    A * (D.act σ) ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 *
              ((AutomorphicForm.borelDiagFst ⟨b, hb⟩)⁻¹ : (AdeleRing (𝓞 L) L)ˣ)) =
      B * ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 *
              ((AutomorphicForm.borelDiagFst ⟨b, hb⟩)⁻¹ : (AdeleRing (𝓞 L) L)ˣ)) + E ∧
    (∏ i ∈ Finset.range (Module.finrank K L), (⇑(D.act σ))^[i] B =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L
        (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0))) *
      ∏ i ∈ Finset.range (Module.finrank K L), (⇑(D.act σ))^[i] A) ∧
    (∀ r : AdeleRing (𝓞 L) L, (⇑(D.act σ))^[Module.finrank K L] r = r) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isUnit_and_mul_act_eq_add_and_prod_iterate_act_eq_norm_mul_of_mem_adelicBorel_of_diagonal.solution
