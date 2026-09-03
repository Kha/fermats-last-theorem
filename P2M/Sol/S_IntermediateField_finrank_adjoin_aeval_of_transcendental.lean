import Mathlib
import P2M.Util
namespace P2MW.S_IntermediateField_finrank_adjoin_aeval_of_transcendental

set_option autoImplicit false

open Polynomial

namespace GaussPencil
namespace Mu

theorem finrank_map_algEquiv {F L L' : Type*} [Field F] [Field L] [Field L'] [Algebra F L] [Algebra F L']
    (e : L ≃ₐ[F] L') (S : IntermediateField F L) :
    Module.finrank ↥(S.map (e : L →ₐ[F] L')) L' = Module.finrank ↥S L := by
  refine (Algebra.finrank_eq_of_equiv_equiv (S.equivMap (e : L →ₐ[F] L')).toRingEquiv e.toRingEquiv ?_).symm
  ext x
  rfl

theorem finrank_adjoin_algebraMap_ratFunc (K : Type*) [Field K] (p : K[X]) (hp : 0 < p.natDegree) :
    Module.finrank ↥(IntermediateField.adjoin K ({algebraMap K[X] (RatFunc K) p} : Set (RatFunc K))) (RatFunc K)
      = p.natDegree := by
  rw [RatFunc.finrank_eq_max_natDegree, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, natDegree_one,
    max_eq_left (Nat.zero_le _)]

theorem algEquiv_algebraMap {K L : Type*} [Field K] [Field L] [Algebra K L] (e : RatFunc K ≃ₐ[K] L) (p : K[X]) :
    e (algebraMap K[X] (RatFunc K) p) = aeval (e RatFunc.X) p := by
  rw [aeval_algHom_apply, RatFunc.aeval_X_left_eq_algebraMap]

end GaussPencil.Mu

theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (s : L) (hs : Transcendental K s) (hgen : IntermediateField.adjoin K ({s} : Set L) = ⊤)
    (p : K[X]) (hp : 0 < p.natDegree) :
    Module.finrank ↥(IntermediateField.adjoin K ({Polynomial.aeval s p} : Set L)) L = p.natDegree := by
  obtain ⟨e, heX⟩ : ∃ e : RatFunc K ≃ₐ[K] L, e RatFunc.X = s :=
    ⟨(RatFunc.algEquivOfTranscendental s hs).trans
      ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv), by simp⟩
  have hmap : (IntermediateField.adjoin K ({algebraMap K[X] (RatFunc K) p} : Set (RatFunc K))).map
      (e : RatFunc K →ₐ[K] L) = IntermediateField.adjoin K ({aeval s p} : Set L) := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    show IntermediateField.adjoin K ({e (algebraMap K[X] (RatFunc K) p)} : Set L) = _
    rw [GaussPencil.Mu.algEquiv_algebraMap, heX]
  rw [← hmap, GaussPencil.Mu.finrank_map_algEquiv, GaussPencil.Mu.finrank_adjoin_algebraMap_ratFunc K p hp]
