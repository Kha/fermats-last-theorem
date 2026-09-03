import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_ModularCurve_GeometricBaseChange
import P2M.Util
import P2M.Sol.S_ModularCurve_map_differentialCorrespondence_eq_heckeDiffBar_map

set_option autoImplicit false

open scoped TensorProduct
open KaehlerDifferential AlgebraicCurve ModularCurve
namespace ModularCurve
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem map_differentialCorrespondence_eq_heckeDiffBar_map
    (p : ℕ) [NeZero p] (q : Nat.Primes) [NeZero (q : ℕ)] [NeZero (p * (q : ℕ))]
    (φα φβ : ↥(modularFunctionFieldFull p) →+* ↥(modularFunctionFieldFull (p * (q : ℕ))))
    (hα : ∀ f : ↥(modularFunctionFieldFull p),
      heckeAlphaBar (AlgebraicClosure ℚ) p q
          (ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p) (1 ⊗ₜ f)) =
        ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull (p * (q : ℕ))) (1 ⊗ₜ φα f))
    (hβ : ∀ f : ↥(modularFunctionFieldFull p),
      heckeBetaBar (AlgebraicClosure ℚ) p q
          (ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p) (1 ⊗ₜ f)) =
        ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull (p * (q : ℕ))) (1 ⊗ₜ φβ f))
    (hfin : FiniteAlong ℚ φβ.toRatAlgHom)
    (ω : Ω[↥(modularFunctionFieldFull p)⁄ℚ]) :
    ((KaehlerDifferential.map ℚ (AlgebraicClosure ℚ)
          ↥(modularFunctionFieldBar p) ↥(modularFunctionFieldBar p)).restrictScalars ℚ)
      (Differential.pullbackAlong
        (((ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p)).toAlgHom.restrictScalars ℚ).comp
          (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ) (B := ↥(modularFunctionFieldFull p))))
        (Differential.correspondence φβ.toRatAlgHom φα.toRatAlgHom ω)) =
    heckeDiffBar p q
      (((KaehlerDifferential.map ℚ (AlgebraicClosure ℚ)
            ↥(modularFunctionFieldBar p) ↥(modularFunctionFieldBar p)).restrictScalars ℚ)
        (Differential.pullbackAlong
          (((ModularCurve.baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p)).toAlgHom.restrictScalars ℚ).comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ) (B := ↥(modularFunctionFieldFull p)))) ω)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_map_differentialCorrespondence_eq_heckeDiffBar_map.solution
end ModularCurve
