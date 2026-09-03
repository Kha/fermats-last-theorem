import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_faithfullyFlat_hopfKer_of_finitePartIdempotent
import Theorems.Thm_HopfAlgebra_isHopfGalois_of_isCocomm_of_finiteType_of_surjective
import Theorems.Thm_HopfAlgebra_isHopfGalois_of_isHopfGalois_baseChange_of_flat
import P2M.Util
namespace P2MW.S_HopfAlgebra_isHopfGalois_of_finitePartIdempotent
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

set_option maxHeartbeats 1600000
set_option autoImplicit false

open scoped TensorProduct

universe u v w

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
    (hee' : qc e = e')
    (f : H) (hf : IsIdempotentElem f) (hfK : f ∈ HopfAlgebra.hopfKer qc) (hfe : f * e = e)
    (hmin : ∀ b ∈ HopfAlgebra.hopfKer qc, b * e = 0 → b * f = 0) :
    HopfAlgebra.IsHopfGalois qc  := by

  haveI : Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) H :=
    HopfAlgebra.faithfullyFlat_hopfKer_of_finitePartIdempotent R K H H' qc hqc e he hfin hgen e' he' hfin' hgen'
      hee' f hf hfK hfe hmin

  let qcK := (Bialgebra.TensorProduct.map (BialgHom.id K K) qc : TensorProduct R K H →ₐc[K] TensorProduct R K H')
  have hqcK_tmul : ∀ (k : K) (h : H), qcK (k ⊗ₜ[R] h) = k ⊗ₜ[R] qc h := fun _ _ => rfl
  have hsurjK : Function.Surjective qcK := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul k h' =>
        obtain ⟨h, rfl⟩ := hqc h'
        exact ⟨k ⊗ₜ[R] h, hqcK_tmul k h⟩
    | add x y hx hy =>
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        exact ⟨x' + y', map_add _ _ _⟩
  have hK : HopfAlgebra.IsHopfGalois qcK :=
    HopfAlgebra.isHopfGalois_of_isCocomm_of_finiteType_of_surjective K (TensorProduct R K H) (TensorProduct R K H')
      qcK hsurjK
  exact HopfAlgebra.isHopfGalois_of_isHopfGalois_baseChange_of_flat K qc hqc hK
