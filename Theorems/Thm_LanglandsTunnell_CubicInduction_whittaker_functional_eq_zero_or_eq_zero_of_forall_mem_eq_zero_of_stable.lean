import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_whittaker_functional_eq_zero_or_eq_zero_of_forall_mem_eq_zero_of_stable

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction~exists_eq_smul_of_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul~exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem"

theorem LanglandsTunnell.CubicInduction.whittaker_functional_eq_zero_or_eq_zero_of_forall_mem_eq_zero_of_stable
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (ψ : AddChar (p.adicCompletion ℚ) ℂ) (hψ : ψ ≠ 1)
    (V : Submodule ℂ ↥(principalSeries2 p θ))
    (hV : ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)), ∀ v ∈ V, principalSeries2Rep θ g v ∈ V) :
    (∀ ℓ : ↥V →ₗ[ℂ] ℂ,
        (∀ (x : p.adicCompletion ℚ) (v : ↥V),
          ℓ ⟨principalSeries2Rep θ (upperUnipotent2 p x) v, hV _ v v.2⟩ = ψ x * ℓ v) → ℓ = 0) ∨
    (∀ L : ↥(principalSeries2 p θ) →ₗ[ℂ] ℂ,
        (∀ (x : p.adicCompletion ℚ) (f : ↥(principalSeries2 p θ)), L (principalSeries2Rep θ (upperUnipotent2 p x) f) = ψ x * L f) →
        (∀ v ∈ V, L v = 0) → L = 0) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_whittaker_functional_eq_zero_or_eq_zero_of_forall_mem_eq_zero_of_stable.solution
