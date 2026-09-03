import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import P2M.Util
import P2M.Sol.S_ModularCurve_CharPReduction_exists_coeffMap_eq_of_mem_modularLocalized_of_monic
set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.CharPReduction.exists_coeffMap_eq_of_mem_modularLocalized_of_monic
    {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (f : LaurentSeries (AlgebraicClosure ℚ))
    (hf : f ∈ CharPReduction.modularLocalized N A.toSubring red)
    (hint : ∃ P : Polynomial (Polynomial A), P.Monic ∧
      Polynomial.eval₂ (Polynomial.eval₂RingHom
        ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
        (jqModC (AlgebraicClosure ℚ))) f P = 0) :
    ∃ y : LaurentSeries A, coeffMap A.subtype y = f := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPReduction_exists_coeffMap_eq_of_mem_modularLocalized_of_monic.solution
