import Mathlib
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_finrank_adjoin_eq_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C

set_option autoImplicit false

open ModularCurve Polynomial

universe u

theorem ModularCurve.finrank_adjoin_eq_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C
    (κ : Type u) [Field κ] (ℓ : ℕ) [Fact ℓ.Prime] (ζ : κˣ) (hζ : IsPrimitiveRoot (ζ : κ) ℓ)
    (F : IntermediateField κ (LaurentSeries κ))
    (hF : ∀ f : LaurentSeries κ, f ∈ F → ModularCurve.qTwist ζ f = f)
    (x r : LaurentSeries κ) (hx : ModularCurve.qTwist ζ x ≠ x)
    (P : Polynomial ↥F)
    (hP : P.map (algebraMap ↥F (LaurentSeries κ)) =
      (∏ k ∈ Finset.range ℓ, (Polynomial.X - Polynomial.C (ModularCurve.qTwist (ζ ^ k) x))) *
        (Polynomial.X - Polynomial.C r)) :
    (r ∉ F → Module.finrank ↥F ↥(IntermediateField.adjoin ↥F ({x} : Set (LaurentSeries κ))) = ℓ + 1) ∧
    (r ∈ F → Module.finrank ↥F ↥(IntermediateField.adjoin ↥F ({x} : Set (LaurentSeries κ))) = ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_adjoin_eq_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C.solution
