import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_Mumford_div_mem_invariantFieldOf_of_smul_eq_algebraMap_mul

set_option autoImplicit false

open CerednikDrinfeld.Mumford

theorem solution
    (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
    [MulSemiringAction G M] [SMulCommClass G K M] [IsDomain M]
    (Γ : Subgroup G) (u : G → K) (x y : FractionRing M)
    (hx : ∀ γ : G, γ ∈ Γ → γ • x = algebraMap K (FractionRing M) (u γ) * x)
    (hy : ∀ γ : G, γ ∈ Γ → γ • y = algebraMap K (FractionRing M) (u γ) * y) :
    x / y ∈ invariantFieldOf K G M Γ := by
  rw [mem_invariantFieldOf_iff]
  intro γ hγ
  by_cases hu : u γ = 0
  ·
    have hx0 : x = 0 := by
      have h := hx γ hγ
      rw [hu, map_zero, zero_mul] at h
      exact (smul_eq_zero_iff_eq γ).1 h
    rw [hx0, zero_div, smul_zero]
  · have hc : algebraMap K (FractionRing M) (u γ) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K (FractionRing M)).injective).2 hu
    rw [div_eq_mul_inv, smul_mul', smul_inv'', hx γ hγ, hy γ hγ, mul_inv, mul_assoc, mul_left_comm x,
      ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
