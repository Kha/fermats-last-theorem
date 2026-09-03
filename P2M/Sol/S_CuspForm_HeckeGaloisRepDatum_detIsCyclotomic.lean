import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_GaloisRep_LocalConditions
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_of_forall_frobenius_det_eq
import P2M.Util
namespace P2MW.S_CuspForm_HeckeGaloisRepDatum_detIsCyclotomic
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open Polynomial

section Datum

variable {p : ℕ} {N : ℕ} [NeZero N] {S : Finset ℕ}
  {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪}
  {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
  [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)]
  [Module.Finite 𝒪 T] [Module.Free 𝒪 T]

theorem solution (hp : p.Prime)
    (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (H : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ T) :
    H.ρ.DetIsCyclotomic p := by
  refine H.ρ.detIsCyclotomic_of_forall_frobenius_det_eq hp ?_ (S ∪ N.primeFactors) ?_
  ·
    rw [IsLocalRing.mem_maximalIdeal] at hp𝒪 ⊢
    rw [show ((p : ℕ) : T) = algebraMap 𝒪 T ((p : ℕ) : 𝒪) from (map_natCast (algebraMap 𝒪 T) p).symm]
    exact fun hu => hp𝒪 (IsLocalHom.map_nonunit _ hu)
  ·
    intro ℓ hℓ hℓS' B τ hB hτ
    simp only [Finset.mem_union, not_or] at hℓS'
    obtain ⟨hℓS, hℓN⟩ := hℓS'
    have hℓN' : ¬ ℓ ∣ N := fun hdvd => hℓN (Nat.mem_primeFactors.mpr ⟨hℓ, hdvd, NeZero.ne N⟩)
    have hcp := H.charpoly_frob ℓ hℓ hℓN' (by exact_mod_cast hℓS) B hB τ hτ

    rw [LinearMap.det_eq_sign_charpoly_coeff, H.ρ.finrank_eq, hcp]
    ring_nf
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]

end Datum
