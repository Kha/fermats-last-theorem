import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
namespace P2MW.S_ModularCurve_exists_monic_natDegree_le_aeval_jqModC_eq_zero
set_option autoImplicit false
open Polynomial IntermediateField
namespace ModularCurve
p2m_export "ModularCurve" "jqNModC_rat coeffMap_jqModC coeffMap_jqNModC jqModC jqNModC jqModC_rat jq jqN dedekindPsi ModularPolynomialData coeffMap coeffMap_coeff EvalSymm"
p2m_open "ModularCurve"

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  rw [← coeffMap_coeff, ← coeffMap_coeff, h]

theorem map_eval₂_aeval_toRingHom {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]
    (g : A →+* B) (Φ : Polynomial (Polynomial ℤ)) (a b : A) :
    g (Φ.eval₂ (aeval (R := ℤ) a).toRingHom b) = Φ.eval₂ (aeval (R := ℤ) (g a)).toRingHom (g b) := by
  rw [hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp

theorem exists_monic_aeval_jqModC_eq_zero_of_modularPolynomialData
    (K : Type*) [Field K] (p : ℕ) [NeZero p]
    (data : ModularPolynomialData p) (hsym : EvalSymm data.Φ) :
    ∃ P : Polynomial K⟮jqNModC K p⟯, P.Monic ∧ P.natDegree = dedekindPsi p ∧
      Polynomial.aeval (jqModC K) P = 0 := by

  let jN : K⟮jqNModC K p⟯ := ⟨jqNModC K p, mem_adjoin_simple_self K _⟩
  let φ : Polynomial ℤ →+* K⟮jqNModC K p⟯ := (aeval (R := ℤ) jN).toRingHom
  refine ⟨data.Φ.map φ, data.monic.map φ, by rw [data.monic.natDegree_map, data.natDegree_eq], ?_⟩

  have h0 : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC ℚ p)).toRingHom (jqModC ℚ) = 0 := by
    rw [jqNModC_rat, jqModC_rat, hsym (jqN p) jq]
    exact data.eval_eq_zero

  have hZ : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC ℤ p)).toRingHom (jqModC ℤ) = 0 := by
    apply coeffMap_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
    rw [map_eval₂_aeval_toRingHom, coeffMap_jqNModC, coeffMap_jqModC, h0, map_zero]

  have hK : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC K p)).toRingHom (jqModC K) = 0 := by
    have := congrArg (coeffMap (Int.castRingHom K)) hZ
    rwa [map_eval₂_aeval_toRingHom, coeffMap_jqNModC, coeffMap_jqModC, map_zero] at this

  have hcomp : (algebraMap K⟮jqNModC K p⟯ (LaurentSeries K)).comp φ =
      (aeval (R := ℤ) (jqNModC K p)).toRingHom := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [φ, jN]
  rw [aeval_def, eval₂_map, hcomp]
  exact hK

private theorem solution_impl
    (K : Type*) [Field K] (p : ℕ) [NeZero p]
    (data : ModularPolynomialData p) (hsym : EvalSymm data.Φ) (hpsi : dedekindPsi p = p + 1) :
    ∃ P : Polynomial K⟮jqNModC K p⟯, P.Monic ∧ P.natDegree ≤ p + 1 ∧
      Polynomial.aeval (jqModC K) P = 0 := by
  obtain ⟨P, hPm, hPdeg, hPj⟩ := exists_monic_aeval_jqModC_eq_zero_of_modularPolynomialData K p data hsym
  exact ⟨P, hPm, by rw [hPdeg, hpsi], hPj⟩

end ModularCurve

theorem solution (K : Type*) [Field K] (p : ℕ) [NeZero p]
    (data : ModularCurve.ModularPolynomialData p) (hsym : ModularCurve.EvalSymm data.Φ)
    (hpsi : ModularCurve.dedekindPsi p = p + 1) :
    ∃ P : Polynomial (IntermediateField.adjoin K ({ModularCurve.jqNModC K p} :
        Set (LaurentSeries K))),
      P.Monic ∧ P.natDegree ≤ p + 1 ∧ Polynomial.aeval (ModularCurve.jqModC K) P = 0 :=
  ModularCurve.solution_impl K p data hsym hpsi
