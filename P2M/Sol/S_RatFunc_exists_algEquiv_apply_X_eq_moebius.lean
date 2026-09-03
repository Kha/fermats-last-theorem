import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.IntermediateField
import P2M.Util
namespace P2MW.S_RatFunc_exists_algEquiv_apply_X_eq_moebius

open Polynomial IntermediateField

namespace RatFunc
p2m_export "RatFunc" "X algebraMap_C algEquivOfTranscendental transcendental adjoin_X C algEquivOfTranscendental_X algebraMap_eq_C transcendental_of_ne_C C_injective transcendental_X"
p2m_open "RatFunc"

variable {K : Type*} [Field K]

theorem moebius_aux (a b c d : K) (hdet : a * d - b * c ≠ 0) :
    ∃ φ : RatFunc K ≃ₐ[K] RatFunc K,
      φ X = (C a * X + C b) / (C c * X + C d) := by
  set f : RatFunc K := (C a * X + C b) / (C c * X + C d) with hf
  have hden : (C c * X + C d : RatFunc K) ≠ 0 := by
    intro h
    have h1 : (C c * X + C d : RatFunc K) = algebraMap K[X] (RatFunc K) (Polynomial.C c * Polynomial.X + Polynomial.C d) := by
      simp [map_add, map_mul]
    rw [h1, map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))] at h
    have hc : c = 0 := by simpa using congrArg (fun p : K[X] ↦ p.coeff 1) h
    have hd : d = 0 := by simpa using congrArg (fun p : K[X] ↦ p.coeff 0) h
    apply hdet; rw [hc, hd]; ring

  have hkey : (C a - C c * f) * (C c * X + C d) = C (a * d - b * c) := by
    rw [hf, sub_mul, mul_assoc, div_mul_cancel₀ _ hden, map_sub, map_mul, map_mul]; ring
  have hac : (C a - C c * f : RatFunc K) ≠ 0 := by
    intro h; rw [h, zero_mul, eq_comm, map_eq_zero_iff _ C_injective] at hkey; exact hdet hkey
  have hX : (X : RatFunc K) = (C d * f - C b) / (C a - C c * f) := by
    rw [eq_div_iff hac]
    have : (C d * f - C b) * (C c * X + C d) = X * C (a * d - b * c) := by
      rw [sub_mul, mul_assoc, hf, div_mul_cancel₀ _ hden, map_sub, map_mul, map_mul]; ring
    have h2 := congrArg (· * (C c * X + C d)) (show (X : RatFunc K) * (C a - C c * f) = X * (C a - C c * f) from rfl)
    apply mul_right_cancel₀ hden
    rw [mul_assoc, hkey, this]

  have hfC : ¬ ∃ e : K, f = C e := by
    rintro ⟨e, he⟩
    have : ∃ e' : K, (X : RatFunc K) = C e' := by
      refine ⟨(d * e - b) / (a - c * e), ?_⟩
      rw [hX, he, ← map_mul, ← map_sub, ← map_mul, ← map_sub, ← map_div₀]
    obtain ⟨e', he'⟩ := this
    have halg : IsAlgebraic K (X : RatFunc K) := by
      rw [he', ← RatFunc.algebraMap_eq_C]
      exact isAlgebraic_algebraMap e'
    exact RatFunc.transcendental_X halg
  have htr : Transcendental K f := transcendental_of_ne_C f hfC

  have hXmem : (X : RatFunc K) ∈ K⟮f⟯ := by
    rw [hX]
    have hfmem : f ∈ K⟮f⟯ := mem_adjoin_simple_self K f
    have hCmem : ∀ e : K, (C e : RatFunc K) ∈ K⟮f⟯ := fun e ↦ by
      rw [← algebraMap_C]; exact (K⟮f⟯).algebraMap_mem e
    exact div_mem (sub_mem (mul_mem (hCmem d) hfmem) (hCmem b)) (sub_mem (hCmem a) (mul_mem (hCmem c) hfmem))
  have htop : K⟮f⟯ = ⊤ := by
    rw [eq_top_iff, ← RatFunc.adjoin_X (K := K), adjoin_simple_le_iff]
    exact hXmem
  refine ⟨(algEquivOfTranscendental f htr).trans ((equivOfEq htop).trans topEquiv), ?_⟩
  simp [algEquivOfTranscendental_X]

end RatFunc

theorem solution {K : Type*} [Field K] (a b c d : K) (hdet : a * d - b * c ≠ 0) : ∃ φ : RatFunc K ≃ₐ[K] RatFunc K, φ RatFunc.X = (RatFunc.C a * RatFunc.X + RatFunc.C b) / (RatFunc.C c * RatFunc.X + RatFunc.C d) :=
  RatFunc.moebius_aux a b c d hdet

#print axioms solution
