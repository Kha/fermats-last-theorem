module

public import Definitions.Def_ModularCurve_HeckeOperator
public import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Sol.S_ModularCurve_geomAut_atkinLehner_comp_legs
import P2M.Sol.S_ModularCurve_exists_isFrickeAutFull_of_neZero
import P2M.Util
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

namespace P2MW.S_ModularCurve_frickeInvolutionBar_comp_heckeAlphaBar_one

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

namespace Ws14Fricke

theorem isAtkinLehnerAutFull_one_of_isFrickeAutFull (q : ℕ) [NeZero q]
    {σ : modularFunctionFieldFull (1 * q) ≃ₐ[ℚ] modularFunctionFieldFull (1 * q)}
    (hσ : IsFrickeAutFull (1 * q) σ) : IsAtkinLehnerAutFull 1 q σ := by
  intro d _ hd
  obtain rfl : d = 1 := Nat.dvd_one.mp hd
  exact ⟨hσ 1 (1 * q) (one_mul _) inferInstance inferInstance,
    hσ (1 * q) 1 (mul_one _) inferInstance inferInstance⟩

theorem isAtkinLehnerAutFull_one_frickeInvolutionFull (q : ℕ) [NeZero q] :
    IsAtkinLehnerAutFull 1 q (frickeInvolutionFull (1 * q)) :=
  isAtkinLehnerAutFull_one_of_isFrickeAutFull q
    (isFrickeAutFull_frickeInvolutionFull (1 * q) (exists_isFrickeAutFull_of_neZero (1 * q)))
end Ws14Fricke

theorem solution (q : ℕ) [NeZero q] :
    (frickeInvolutionBar (1 * q)).toAlgHom.comp (heckeAlphaBar (AlgebraicClosure ℚ) 1 q)
      = heckeBetaBar (AlgebraicClosure ℚ) 1 q :=
  (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) 1 q (frickeInvolutionFull (1 * q))
    (Ws14Fricke.isAtkinLehnerAutFull_one_frickeInvolutionFull q)).1
end S_ModularCurve_frickeInvolutionBar_comp_heckeAlphaBar_one
end P2MW

public section
set_option autoImplicit false

open AlgebraicCurve ModularCurve
theorem ModularCurve.frickeInvolutionBar_comp_heckeAlphaBar_one (q : ℕ) [NeZero q] :
    (frickeInvolutionBar (1 * q)).toAlgHom.comp (heckeAlphaBar (AlgebraicClosure ℚ) 1 q)
      = heckeBetaBar (AlgebraicClosure ℚ) 1 q := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_frickeInvolutionBar_comp_heckeAlphaBar_one.solution
end
