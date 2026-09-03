import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_Iso_subsingleton

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Q Q' : DrinfeldDatum (K := K) π B) : Subsingleton (Q.Iso Q') := by
  classical
  refine ⟨fun I I' => ?_⟩

  have h0 : I.τ₀ = I'.τ₀ := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro t
    apply Module.eq_of_localization_maximal (fun (P : Ideal B) _ => LocalizedModule P.primeCompl Q'.T₀)
      (fun (P : Ideal B) _ => LocalizedModule.mkLinearMap P.primeCompl Q'.T₀)
    intro P hP
    let x : PrimeSpectrum B := ⟨P, hP.isPrime⟩
    have key : ∀ w : stalk B x Q.T₀,
        LocalizedModule.map x.asIdeal.primeCompl I.τ₀.toLinearMap w = LocalizedModule.map x.asIdeal.primeCompl I'.τ₀.toLinearMap w := by
      intro w
      obtain ⟨z, rfl⟩ := Q.u₀_surjective x w
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul b v =>
        have hv' : (v : Fin 2 → K) ∈ Q'.N₀ x := by rw [← I.N₀_eq]; exact v.2
        have e : b ⊗ₜ[𝒪] v = b • ((1 : locRing B x) ⊗ₜ[𝒪] v) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [e, map_smul, map_smul, map_smul]
        have h1 := I.τ₀_u₀ x v v.2 hv'
        have h2 := I'.τ₀_u₀ x v v.2 hv'
        rw [Subtype.coe_eta] at h1 h2
        rw [← h1, ← h2]
      | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    have := key (LocalizedModule.mkLinearMap x.asIdeal.primeCompl Q.T₀ t)
    rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk, LocalizedModule.map_mk] at this
    exact this

  have h1 : I.τ₁ = I'.τ₁ := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro t
    apply Module.eq_of_localization_maximal (fun (P : Ideal B) _ => LocalizedModule P.primeCompl Q'.T₁)
      (fun (P : Ideal B) _ => LocalizedModule.mkLinearMap P.primeCompl Q'.T₁)
    intro P hP
    let x : PrimeSpectrum B := ⟨P, hP.isPrime⟩
    have key : ∀ w : stalk B x Q.T₁,
        LocalizedModule.map x.asIdeal.primeCompl I.τ₁.toLinearMap w = LocalizedModule.map x.asIdeal.primeCompl I'.τ₁.toLinearMap w := by
      intro w
      obtain ⟨z, rfl⟩ := Q.u₁_surjective x w
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul b v =>
        have hv' : (v : Fin 2 → K) ∈ Q'.N₁ x := by rw [← I.N₁_eq]; exact v.2
        have e : b ⊗ₜ[𝒪] v = b • ((1 : locRing B x) ⊗ₜ[𝒪] v) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [e, map_smul, map_smul, map_smul]
        have h1 := I.τ₁_u₁ x v v.2 hv'
        have h2 := I'.τ₁_u₁ x v v.2 hv'
        rw [Subtype.coe_eta] at h1 h2
        rw [← h1, ← h2]
      | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    have := key (LocalizedModule.mkLinearMap x.asIdeal.primeCompl Q.T₁ t)
    rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk, LocalizedModule.map_mk] at this
    exact this

  cases I; cases I'
  simp only at h0 h1
  subst h0; subst h1
  rfl
