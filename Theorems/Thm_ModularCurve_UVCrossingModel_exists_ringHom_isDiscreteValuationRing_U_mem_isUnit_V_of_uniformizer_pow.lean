import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_ringHom_isDiscreteValuationRing_U_mem_isUnit_V_of_uniformizer_pow

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.exists_ringHom_isDiscreteValuationRing_U_mem_isUnit_V_of_uniformizer_pow
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) :
    ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsDiscreteValuationRing D)
      (ψ : UVCrossingModel W (ϖ ^ e) →+* D),
      Function.Injective ψ ∧
      ψ (U (ϖ ^ e)) ∈ maximalIdeal D ∧
      IsUnit (ψ (V (ϖ ^ e))) ∧
      maximalIdeal D = Ideal.span {ψ (const (ϖ ^ e) ϖ)} ∧
      (∀ x : UVCrossingModel W (ϖ ^ e), ψ x ∈ maximalIdeal D ↔ x ∈ Ideal.span {U (ϖ ^ e), const (ϖ ^ e) ϖ}) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringHom_isDiscreteValuationRing_U_mem_isUnit_V_of_uniformizer_pow.solution
