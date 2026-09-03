import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_ringEquiv_prod_forall_act_eq
import P2M.Util
namespace P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_ringEquiv_prod_forall_act_eq_ed2

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    ∃ (A : InfiniteAdeleRing L ≃+* InfiniteAdeleRing L) (B : FiniteAdeleRing (𝓞 L) L ≃+* FiniteAdeleRing (𝓞 L) L),
      Continuous A ∧ Continuous A.symm ∧ Continuous B ∧ Continuous B.symm ∧
      ∀ x : AdeleRing (𝓞 L) L, (D.act σ : RingAut (AdeleRing (𝓞 L) L)) x = (A x.1, B x.2) := by
  obtain ⟨A, B, hA, hB, hAB⟩ := M4aHerbrand.IdeleGaloisDescent.exists_ringEquiv_prod_forall_act_eq K L D σ
  obtain ⟨A', B', hA', hB', hAB'⟩ := M4aHerbrand.IdeleGaloisDescent.exists_ringEquiv_prod_forall_act_eq K L D σ⁻¹
  have hcomp : ∀ w : AdeleRing (𝓞 L) L,
      (D.act σ : RingAut (AdeleRing (𝓞 L) L)) ((D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) w) = w := by
    intro w
    rw [← RingAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, RingAut.one_apply]
  have hpair : ∀ (y : InfiniteAdeleRing L) (z : FiniteAdeleRing (𝓞 L) L), (A (A' y), B (B' z)) = (y, z) := by
    intro y z
    have h := hcomp (y, z)
    rw [hAB' (y, z), hAB] at h
    exact h
  have hAs : (A.symm : InfiniteAdeleRing L → InfiniteAdeleRing L) = A' := by
    funext y
    have h := congrArg Prod.fst (hpair y 0)
    simp only at h
    rw [← h, RingEquiv.symm_apply_apply]

    rw [h]
  have hBs : (B.symm : FiniteAdeleRing (𝓞 L) L → FiniteAdeleRing (𝓞 L) L) = B' := by
    funext z
    have h := congrArg Prod.snd (hpair 0 z)
    simp only at h
    rw [← h, RingEquiv.symm_apply_apply, h]
  refine ⟨A, B, hA, ?_, hB, ?_, hAB⟩
  · rw [hAs]; exact hA'
  · rw [hBs]; exact hB'
