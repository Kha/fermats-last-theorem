import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm

set_option autoImplicit false
open NumberField M4aHerbrand M4aHerbrand.GenuineDescent

theorem M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F) :
    Function.Injective (genuineBaseChange E F).β ∧
    (∀ u : (AdeleRing (𝓞 F) F)ˣ, (∀ τ : F ≃ₐ[E] F, D.unitsAct τ u = u) ↔
      u ∈ (Units.map (genuineBaseChange E F).β.toMonoidHom).range) ∧
    (∀ u : (AdeleRing (𝓞 F) F)ˣ,
      (∀ τ : F ≃ₐ[E] F, (D.unitsAct τ u)⁻¹ * u ∈ principalIdeles (𝓞 F) F) →
      u ∈ (Units.map (genuineBaseChange E F).β.toMonoidHom).range ⊔ principalIdeles (𝓞 F) F) ∧
    (∀ u : (AdeleRing (𝓞 F) F)ˣ,
      ∏ τ : F ≃ₐ[E] F, D.unitsAct τ u =
        Units.map (genuineBaseChange E F).β.toMonoidHom ((genuineBaseChange E F).idelicNorm u)) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm.solution
