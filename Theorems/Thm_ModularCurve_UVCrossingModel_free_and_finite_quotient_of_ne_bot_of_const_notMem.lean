import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_free_and_finite_quotient_of_ne_bot_of_const_notMem

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem ModularCurve.UVCrossingModel.free_and_finite_quotient_of_ne_bot_of_const_notMem
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (Q : Ideal (UVCrossingModel W (π ^ E))) [Q.IsPrime] (hQ0 : Q ≠ ⊥) (hQπ : const (π ^ E) π ∉ Q) :
    Module.Free W (UVCrossingModel W (π ^ E) ⧸ Q) ∧ Module.Finite W (UVCrossingModel W (π ^ E) ⧸ Q) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_free_and_finite_quotient_of_ne_bot_of_const_notMem.solution
