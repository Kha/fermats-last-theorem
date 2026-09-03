import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul
set_option Elab.async false
set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.map_hopfKer_eq_hopfKer_of_finitePartIdempotent
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
    (hmin : ∀ b ∈ HopfAlgebra.hopfKer qc, b * e = 0 → b * f = 0)
    (Hf : Type) [CommRing Hf] [HopfAlgebra R Hf] (πf : H →ₐc[R] Hf) (hπf : Function.Surjective πf)
    (hkerf : RingHom.ker (πf : H →ₐ[R] Hf) = Ideal.span {1 - e})
    (Hf' : Type) [CommRing Hf'] [HopfAlgebra R Hf'] (πf' : H' →ₐc[R] Hf') (hπf' : Function.Surjective πf')
    (hkerf' : RingHom.ker (πf' : H' →ₐ[R] Hf') = Ideal.span {1 - e'})
    (qcf : Hf →ₐc[R] Hf') (hcomm : ∀ x : H, qcf (πf x) = πf' (qc x)) :
    (HopfAlgebra.hopfKer qc).map (πf : H →ₐ[R] Hf) = HopfAlgebra.hopfKer qcf := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_finitePartIdempotent.solution
