import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_HeckeCharacter_eq_of_forall_apply_localUnit_uniformizerUnit_eq

open NumberField IsDedekindDomain

theorem HeckeCharacter.eq_of_forall_apply_localUnit_uniformizerUnit_eq
    (K : Type*) [Field K] [NumberField K]
    (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχ₁ : AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ₁)
    (hχ₂ : AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ₂)
    (hc₁ : Continuous χ₁)
    (hc₂ : Continuous χ₂)
    (𝔣₁ 𝔣₂ : Ideal (𝓞 K))
    (hmod₁ : HeckeCharacter.AdmitsModulus K χ₁ 𝔣₁)
    (hmod₂ : HeckeCharacter.AdmitsModulus K χ₂ 𝔣₂)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S,
      χ₁ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)
          (NumberField.AdelicLevel.localUnit (𝓞 K) K v (NumberField.AdelicLevel.uniformizerUnit K v)))
        = χ₂ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)
          (NumberField.AdelicLevel.localUnit (𝓞 K) K v (NumberField.AdelicLevel.uniformizerUnit K v)))) :
    χ₁ = χ₂ := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_eq_of_forall_apply_localUnit_uniformizerUnit_eq.solution
