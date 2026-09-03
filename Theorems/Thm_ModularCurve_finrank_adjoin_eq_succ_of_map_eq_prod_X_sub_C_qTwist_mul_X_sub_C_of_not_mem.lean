import Mathlib
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_finrank_adjoin_eq_succ_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C_of_not_mem

set_option autoImplicit false

open ModularCurve Polynomial

universe u

theorem ModularCurve.finrank_adjoin_eq_succ_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C_of_not_mem
    (κ : Type u) [Field κ] (ℓ : ℕ) [Fact ℓ.Prime] (ζ : κˣ) (hζ : IsPrimitiveRoot (ζ : κ) ℓ)
    (F : IntermediateField κ (LaurentSeries κ))
    (hF : ∀ f : LaurentSeries κ, f ∈ F → ModularCurve.qTwist ζ f = f)
    (x y : LaurentSeries κ) (hy : ModularCurve.qTwist ζ y ≠ y) (hxσ : ModularCurve.qTwist ζ x = x) (hx : x ∉ F)
    (P : Polynomial ↥F)
    (hP : P.map (algebraMap ↥F (LaurentSeries κ)) =
      (∏ k ∈ Finset.range ℓ, (Polynomial.X - Polynomial.C (ModularCurve.qTwist (ζ ^ k) y))) *
        (Polynomial.X - Polynomial.C x)) :
    Module.finrank ↥F ↥(IntermediateField.adjoin ↥F ({x} : Set (LaurentSeries κ))) = ℓ + 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_adjoin_eq_succ_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C_of_not_mem.solution
