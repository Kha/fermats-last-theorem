import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_N_eq_of_isQuadrupleOf
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_isIsomorphic_of_N_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_of_isIsomorphic
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_isQuadrupleOf_iff_isIsomorphic

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace IsoCompatGlue

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
  {B : Type} [CommRing B] [Algebra 𝒪 B]

noncomputable def isoSymm {Q Q' : DrinfeldDatum (K := K) π B} (e : Q.Iso Q') : Q'.Iso Q where
  N₀_eq x := (e.N₀_eq x).symm
  N₁_eq x := (e.N₁_eq x).symm
  τ₀ := e.τ₀.symm
  τ₁ := e.τ₁.symm
  τ₁_Pi₀ t := by
    apply e.τ₁.injective
    rw [LinearEquiv.apply_symm_apply, e.τ₁_Pi₀, LinearEquiv.apply_symm_apply]
  τ₀_Pi₁ t := by
    apply e.τ₀.injective
    rw [LinearEquiv.apply_symm_apply, e.τ₀_Pi₁, LinearEquiv.apply_symm_apply]
  τ₀_u₀ x v hv hv' := by
    have h := e.τ₀_u₀ x v hv' hv
    have hinv : ∀ y : stalk B x Q.T₀,
        LocalizedModule.map x.asIdeal.primeCompl e.τ₀.symm.toLinearMap
          (LocalizedModule.map x.asIdeal.primeCompl e.τ₀.toLinearMap y) = y := by
      intro y
      induction y using LocalizedModule.induction_on with
      | h m s => simp [LocalizedModule.map_mk]
    rw [h, hinv]
  τ₁_u₁ x v hv hv' := by
    have h := e.τ₁_u₁ x v hv' hv
    have hinv : ∀ y : stalk B x Q.T₁,
        LocalizedModule.map x.asIdeal.primeCompl e.τ₁.symm.toLinearMap
          (LocalizedModule.map x.asIdeal.primeCompl e.τ₁.toLinearMap y) = y := by
      intro y
      induction y using LocalizedModule.induction_on with
      | h m s => simp [LocalizedModule.map_mk]
    rw [h, hinv]

end IsoCompatGlue

open IsoCompatGlue in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    {Q : DrinfeldDatum (K := K) π B} {d : DeligneDatum (K := K) π B} (h : Q.IsQuadrupleOf d)
    (Q' : DrinfeldDatum (K := K) π B) : Q'.IsQuadrupleOf d ↔ Q'.IsIsomorphic Q := by
  constructor
  · intro h'
    exact DrinfeldDatum.IsQuadrupleOf.isIsomorphic_of_N_eq hπ hB h Q' h'
      (fun x => (DrinfeldDatum.IsQuadrupleOf.N_eq_of_isQuadrupleOf hπ hB h Q' h' x).1)
      (fun x => (DrinfeldDatum.IsQuadrupleOf.N_eq_of_isQuadrupleOf hπ hB h Q' h' x).2)
  · rintro ⟨e⟩
    exact DrinfeldDatum.IsQuadrupleOf.of_isIsomorphic h ⟨isoSymm e⟩
