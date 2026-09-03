import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_BaseChangeAlong_exists_iso
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_Iso_subsingleton
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_BaseChangeAlong_tau_unique

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace B25H2

noncomputable def isoRefl {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] (Q : DrinfeldDatum (K := K) π B) : Q.Iso Q where
  N₀_eq _ := rfl
  N₁_eq _ := rfl
  τ₀ := LinearEquiv.refl B Q.T₀
  τ₁ := LinearEquiv.refl B Q.T₁
  τ₁_Pi₀ _ := rfl
  τ₀_Pi₁ _ := rfl
  τ₀_u₀ x v hv hv' := by
    rw [LinearEquiv.refl_toLinearMap, LocalizedModule.map_id]; rfl
  τ₁_u₁ x v hv hv' := by
    rw [LinearEquiv.refl_toLinearMap, LocalizedModule.map_id]; rfl

end B25H2

theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (g : B →ₐ[𝒪] B')
    {Q : DrinfeldDatum (K := K) π B} {Q' : DrinfeldDatum (K := K) π B'}
    (W W' : Q.BaseChangeAlong g Q') :
    (∀ t, W.τ₀ t = W'.τ₀ t) ∧ (∀ t, W.τ₁ t = W'.τ₁ t) := by
  obtain ⟨e, he₀, he₁⟩ := CerednikDrinfeld.FormalOmega.DrinfeldDatum.BaseChangeAlong.exists_iso g W W'
  have hsub := CerednikDrinfeld.FormalOmega.DrinfeldDatum.Iso.subsingleton Q' Q'
  have he : e = B25H2.isoRefl Q' := hsub.elim e _
  subst he
  exact ⟨fun t => (he₀ t).symm.trans rfl |>.symm, fun t => (he₁ t).symm.trans rfl |>.symm⟩
