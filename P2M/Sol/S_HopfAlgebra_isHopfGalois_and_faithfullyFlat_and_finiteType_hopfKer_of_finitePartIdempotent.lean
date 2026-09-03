import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_exists_isIdempotentElem_mem_hopfKer_mul_eq_of_finitePartIdempotent
import Theorems.Thm_HopfAlgebra_finiteType_hopfKer_of_finitePartIdempotent
import Theorems.Thm_HopfAlgebra_faithfullyFlat_hopfKer_of_finitePartIdempotent
import Theorems.Thm_HopfAlgebra_isHopfGalois_of_finitePartIdempotent
import P2M.Util
namespace P2MW.S_HopfAlgebra_isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_finitePartIdempotent
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

set_option autoImplicit false

theorem solution
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
    (hee' : qc e = e') :
    HopfAlgebra.IsHopfGalois qc ∧
      Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) H ∧
      Algebra.FiniteType R ↥(HopfAlgebra.hopfKer qc) := by
  obtain ⟨f, hf, hfK, hfe, hmin⟩ :=
    HopfAlgebra.exists_isIdempotentElem_mem_hopfKer_mul_eq_of_finitePartIdempotent
      R K H H' qc hqc e he hfin hgen e' he' hfin' hgen' hee'
  exact ⟨HopfAlgebra.isHopfGalois_of_finitePartIdempotent R K H H' qc hqc e he hfin hgen e' he' hfin' hgen' hee' f hf hfK hfe hmin,
    HopfAlgebra.faithfullyFlat_hopfKer_of_finitePartIdempotent R K H H' qc hqc e he hfin hgen e' he' hfin' hgen' hee' f hf hfK hfe hmin,
    HopfAlgebra.finiteType_hopfKer_of_finitePartIdempotent R K H H' qc hqc e he hfin hgen e' he' hfin' hgen' hee' f hf hfK hfe hmin⟩
