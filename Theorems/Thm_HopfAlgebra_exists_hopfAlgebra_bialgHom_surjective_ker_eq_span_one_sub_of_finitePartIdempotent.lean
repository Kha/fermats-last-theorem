import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_span_one_sub_of_finitePartIdempotent
set_option autoImplicit false

theorem HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_span_one_sub_of_finitePartIdempotent
    (R : Type) [CommRing R] [IsLocalRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H]
    (e : H) (he : IsIdempotentElem e) (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤) :
    ∃ (Hf : Type) (_ : CommRing Hf) (_ : HopfAlgebra R Hf) (πf : H →ₐc[R] Hf),
      Function.Surjective πf ∧
      RingHom.ker (πf : H →ₐ[R] Hf) = Ideal.span {1 - e} ∧
      (Coalgebra.IsCocomm R H → Coalgebra.IsCocomm R Hf) ∧
      Module.Finite R Hf ∧
      (Module.Flat R H → Module.Flat R Hf) ∧
      (∀ (T : Type) [CommRing T] [Algebra R T] (φ : H →ₐ[R] T), φ e = 1 →
        ∃! φ' : Hf →ₐ[R] T, φ'.comp (πf : H →ₐ[R] Hf) = φ) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_span_one_sub_of_finitePartIdempotent.solution
