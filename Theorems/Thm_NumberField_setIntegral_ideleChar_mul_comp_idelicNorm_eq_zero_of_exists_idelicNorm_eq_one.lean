import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_NumberField_setIntegral_ideleChar_mul_comp_idelicNorm_eq_zero_of_exists_idelicNorm_eq_one

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.setIntegral_ideleChar_mul_comp_idelicNorm_eq_zero_of_exists_idelicNorm_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (Θ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΘ : IsFundamentalDomain
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range Θ νZL)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (hker : ∃ t : (AdeleRing (𝓞 L) L)ˣ,
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm t = 1 ∧ ξ ⟨t, Subgroup.mem_top t⟩ ≠ 1)
    (g : (AdeleRing (𝓞 K) K)ˣ → ℂ) (hg : Measurable g) :
    ∫ z in Θ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL = 0 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_setIntegral_ideleChar_mul_comp_idelicNorm_eq_zero_of_exists_idelicNorm_eq_one.solution
