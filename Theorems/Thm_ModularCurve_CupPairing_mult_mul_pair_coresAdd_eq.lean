import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_CupPairing
import P2M.Util
import P2M.Sol.S_ModularCurve_CupPairing_mult_mul_pair_coresAdd_eq

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.CupPairing.mult_mul_pair_coresAdd_eq (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (K : Subgroup Γ) [K.FiniteIndex]
    (x : Additive Γ →+ ℚ) (xK y' : Additive (K.map Γ.subtype) →+ ℚ) (yK : Additive K →+ ℚ)
    (hx : ModularCurve.Period.IsParabolicHom Γ x)
    (hy' : ModularCurve.Period.IsParabolicHom (K.map Γ.subtype) y')
    (hxK : ∀ k : K, xK (Additive.ofMul ⟨((k : Γ) : SL(2, ℤ)), Subgroup.mem_map_of_mem Γ.subtype k.2⟩) =
      x (Additive.ofMul (k : Γ)))
    (hyK : ∀ k : K, yK (Additive.ofMul k) =
      y' (Additive.ofMul ⟨((k : Γ) : SL(2, ℤ)), Subgroup.mem_map_of_mem Γ.subtype k.2⟩)) :
    ModularCurve.CupPairing.mult Γ * ModularCurve.CupPairing.pair Γ x (CohCarrier.coresAdd K yK) =
      ModularCurve.CupPairing.mult (K.map Γ.subtype) *
        ModularCurve.CupPairing.pair (K.map Γ.subtype) xK y' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CupPairing_mult_mul_pair_coresAdd_eq.solution
