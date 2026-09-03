import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_setIntegral_ideleClassChar_mul_eq_zero_of_isFundamentalDomain_of_forall_mul_eq_of_apply_ne_one

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.setIntegral_ideleClassChar_mul_eq_zero_of_isFundamentalDomain_of_forall_mul_eq_of_apply_ne_one
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξKt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (t : (AdeleRing (𝓞 K) K)ˣ) (ht : ξK ⟨t, Subgroup.mem_top t⟩ ≠ 1)
    (F : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hFK : ∀ γ : (AdeleRing (𝓞 K) K)ˣ,
      γ ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ∀ z : (AdeleRing (𝓞 K) K)ˣ, F (γ * z) = F z)
    (hFt : ∀ z : (AdeleRing (𝓞 K) K)ˣ, F (z * t) = F z) :
    ∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * F z ∂νZK = 0 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_setIntegral_ideleClassChar_mul_eq_zero_of_isFundamentalDomain_of_forall_mul_eq_of_apply_ne_one.solution
