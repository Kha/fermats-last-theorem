import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_smul_of_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul
import P2M.Util
namespace P2MW.S_LanglandsTunnell_CubicInduction_whittaker_functional_eq_zero_or_eq_zero_of_forall_mem_eq_zero_of_stable

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (ψ : AddChar (p.adicCompletion ℚ) ℂ) (hψ : ψ ≠ 1)
    (V : Submodule ℂ ↥(principalSeries2 p θ))
    (hV : ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)), ∀ v ∈ V, principalSeries2Rep θ g v ∈ V) :
    (∀ ℓ : ↥V →ₗ[ℂ] ℂ,
        (∀ (x : p.adicCompletion ℚ) (v : ↥V),
          ℓ ⟨principalSeries2Rep θ (upperUnipotent2 p x) v, hV _ v v.2⟩ = ψ x * ℓ v) → ℓ = 0) ∨
    (∀ L : ↥(principalSeries2 p θ) →ₗ[ℂ] ℂ,
        (∀ (x : p.adicCompletion ℚ) (f : ↥(principalSeries2 p θ)), L (principalSeries2Rep θ (upperUnipotent2 p x) f) = ψ x * L f) →
        (∀ v ∈ V, L v = 0) → L = 0) := by
  classical
  by_cases h : ∀ ℓ : ↥V →ₗ[ℂ] ℂ,
      (∀ (x : p.adicCompletion ℚ) (v : ↥V),
        ℓ ⟨principalSeries2Rep θ (upperUnipotent2 p x) v, hV _ v v.2⟩ = ψ x * ℓ v) → ℓ = 0
  · exact Or.inl h
  · right
    push_neg at h
    obtain ⟨ℓ, hℓ, hℓ0⟩ := h
    intro L hL hLV
    obtain ⟨L₁, hL₁, hL₁V⟩ :=
      LanglandsTunnell.CubicInduction.exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem
        p θ ψ V (fun x u hu => hV _ u hu) ℓ hℓ
    have hL₁0 : L₁ ≠ 0 := by
      intro h0
      apply hℓ0
      ext u
      rw [← hL₁V u, h0, LinearMap.zero_apply, LinearMap.zero_apply]
    obtain ⟨c, hc⟩ :=
      LanglandsTunnell.CubicInduction.exists_eq_smul_of_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul
        p θ ψ hψ L₁ L hL₁ hL hL₁0
    by_cases hc0 : c = 0
    · rw [hc, hc0, zero_smul]
    · exfalso
      apply hℓ0
      ext u
      have h1 := hLV u u.2
      rw [hc, LinearMap.smul_apply, hL₁V, smul_eq_mul] at h1
      rw [LinearMap.zero_apply]
      exact (mul_eq_zero.1 h1).resolve_left hc0
