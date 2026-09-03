import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_AutomorphicForm_TransversalMeasure
import P2M.Util
import P2M.Sol.S_NumberField_Idele_exists_finset_forall_semiLocalCharacter_eq_one_and_eq_mul_prod_semiLocalCharacter_of_continuous

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem NumberField.Idele.exists_finset_forall_semiLocalCharacter_eq_one_and_eq_mul_prod_semiLocalCharacter_of_continuous
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) :
    Continuous (fun a : (InfiniteAdeleRing L)ˣ =>
        ((ξL ⟨Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) a,
          Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) ∧
    ∃ R : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ R →
        ∀ u : (L ⊗[K] v.adicCompletion K)ˣ, u ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v →
          TwistedUnipotentTerm.semiLocalCharacter K L ξL v u = 1) ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), R ⊆ S →
        ∀ t : (AdeleRing (𝓞 L) L)ˣ,
          (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
            AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
              AutomorphicForm.TransversalMeasure.integralUnits K L v) →
          ((ξL ⟨t, Subgroup.mem_top t⟩ : ℂˣ) : ℂ) =
            ((ξL ⟨Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
                (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t),
              Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
            ∏ v ∈ S, TwistedUnipotentTerm.semiLocalCharacter K L ξL v
              (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Idele_exists_finset_forall_semiLocalCharacter_eq_one_and_eq_mul_prod_semiLocalCharacter_of_continuous.solution
