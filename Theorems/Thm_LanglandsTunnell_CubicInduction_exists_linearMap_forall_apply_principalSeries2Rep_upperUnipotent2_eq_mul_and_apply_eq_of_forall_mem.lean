import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem
    (p : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (ψ : AddChar (p.adicCompletion ℚ) ℂ)
    (U : Submodule ℂ ↥(principalSeries2 p χ))
    (hU : ∀ (x : p.adicCompletion ℚ), ∀ u ∈ U, principalSeries2Rep χ (upperUnipotent2 p x) u ∈ U)
    (ℓ : ↥U →ₗ[ℂ] ℂ)
    (hℓ : ∀ (x : p.adicCompletion ℚ) (u : ↥U),
      ℓ ⟨principalSeries2Rep χ (upperUnipotent2 p x) u, hU x u u.2⟩ = ψ x * ℓ u) :
    ∃ L : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ,
      (∀ (x : p.adicCompletion ℚ) (f : ↥(principalSeries2 p χ)),
        L (principalSeries2Rep χ (upperUnipotent2 p x) f) = ψ x * L f) ∧
      ∀ u : ↥U, L (u : ↥(principalSeries2 p χ)) = ℓ u := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem.solution
