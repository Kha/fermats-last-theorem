import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent
set_option Elab.async false
set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H] [Module.Finite K (TensorProduct R K H)]
    (H' : Type) [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc)
    (e : H) (he : IsIdempotentElem e) (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤)
    (e' : H') (he' : IsIdempotentElem e') (hfin' : Module.Finite R (Localization.Away e'))
    (hgen' : Ideal.map (algebraMap R (Localization.Away (1 - e'))) (IsLocalRing.maximalIdeal R) = ⊤)
    (hee' : qc e = e')
    (f : H) (hf : IsIdempotentElem f) (hfK : f ∈ HopfAlgebra.hopfKer qc) (hfe : f * e = e)
    (hmin : ∀ b ∈ HopfAlgebra.hopfKer qc, b * e = 0 → b * f = 0) :
    Module.FaithfullyFlat (↥(HopfAlgebra.hopfKer qc) ⧸ Ideal.span {(⟨f, hfK⟩ : ↥(HopfAlgebra.hopfKer qc))})
      (TensorProduct ↥(HopfAlgebra.hopfKer qc)
        (↥(HopfAlgebra.hopfKer qc) ⧸ Ideal.span {(⟨f, hfK⟩ : ↥(HopfAlgebra.hopfKer qc))}) H) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_faithfullyFlat_quotient_span_orbitIdempotent_baseChange_of_finitePartIdempotent.solution
