import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import P2M.Util
import P2M.Sol.S_LocalNewvector_PSCarrier_exists_forall_stable_iff_of_hasCharConductor_of_ratio_eq_natCast
attribute [-instance] FLT.SpectralSide.instCompactSpaceMatrix
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv

set_option autoImplicit false

theorem LocalNewvector.PSCarrier.exists_forall_stable_iff_of_hasCharConductor_of_ratio_eq_natCast
    (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {c : ℕ}
    (h₁ : LocalNewvector.HasCharConductor p μ₁ c)
    (hrat : LocalNewvector.IsUnramified p (μ₁⁻¹ * μ₂))
    (hγ : (μ₁ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ) *
        ((μ₂ (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) : ℂ))⁻¹
          = (p : ℂ)) :
    ∃ T : LocalNewvector.PSCarrier p μ₁ μ₂,
      (∀ g : GL (Fin 2) ℚ_[p], LocalNewvector.PSCarrier.toFn p μ₁ μ₂ T g =
        (μ₁ (Matrix.GeneralLinearGroup.det g) : ℂ) *
          LocalNewvector.halfModulus p (Matrix.GeneralLinearGroup.det g) 1) ∧
      ∀ W : Submodule ℂ (LocalNewvector.PSCarrier p μ₁ μ₂),
        (∀ g : GL (Fin 2) ℚ_[p], ∀ v ∈ W, g • v ∈ W) ↔
          (W = ⊥ ∨ W = Submodule.span ℂ {T} ∨ W = ⊤) := by p2m_exact_reverting @_root_.P2MW.S_LocalNewvector_PSCarrier_exists_forall_stable_iff_of_hasCharConductor_of_ratio_eq_natCast.solution
