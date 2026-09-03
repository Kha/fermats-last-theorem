import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_JZeroTateModule
import P2M.Util
import P2M.Sol.S_TateModule_exists_linearEquiv_rationalTateModule_comp_rationalGaloisRep_eq_of_addEquiv

set_option autoImplicit false

open AlgebraicCurve

open scoped TensorProduct

theorem TateModule.exists_linearEquiv_rationalTateModule_comp_rationalGaloisRep_eq_of_addEquiv
    (p : ℕ) [Fact p.Prime] {J J' : Type} [AddCommGroup J] [AddCommGroup J'] (Ψ : J ≃+ J')
    (G G' : Type) [Monoid G] [Monoid G'] [DistribMulAction G J] [DistribMulAction G' J'] :
    ∃ Θ : ModularCurve.RationalTateModule p J ≃ₗ[ℚ_[p]] ModularCurve.RationalTateModule p J',
      (∀ x : TateModule p J, ∃ y : TateModule p J',
        Θ ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x) = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y ∧
          ∀ n : ℕ, TateModule.proj p J' n y = Ψ (TateModule.proj p J n x)) ∧
      ∀ (g : G) (g' : G'), (∀ x : J, Ψ (g • x) = g' • Ψ x) →
        (Θ : ModularCurve.RationalTateModule p J →ₗ[ℚ_[p]] ModularCurve.RationalTateModule p J') ∘ₗ
            ModularCurve.rationalGaloisRep p J G g =
          ModularCurve.rationalGaloisRep p J' G' g' ∘ₗ
            (Θ : ModularCurve.RationalTateModule p J →ₗ[ℚ_[p]] ModularCurve.RationalTateModule p J') := by p2m_exact_reverting @_root_.P2MW.S_TateModule_exists_linearEquiv_rationalTateModule_comp_rationalGaloisRep_eq_of_addEquiv.solution
