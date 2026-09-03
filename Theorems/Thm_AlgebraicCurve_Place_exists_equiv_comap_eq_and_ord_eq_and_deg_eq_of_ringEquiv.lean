import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_JZeroTateModule
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv
    {K K' F F' : Type} [Field K] [Field K'] [Field F] [Field F'] [Algebra K F] [Algebra K' F']
    (e : K ≃+* K') (φ : F ≃+* F') (hφ : ∀ a : K, φ (algebraMap K F a) = algebraMap K' F' (e a)) :
    ∃ Φ : Place K F ≃ Place K' F',
      (∀ v : Place K F, (Φ v).toValuationSubring = v.toValuationSubring.comap φ.symm.toRingHom) ∧
      (∀ (v : Place K F) (f : F), (Φ v).ord (φ f) = v.ord f) ∧
      (∀ v : Place K F, (Φ v).deg = v.deg) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv.solution
