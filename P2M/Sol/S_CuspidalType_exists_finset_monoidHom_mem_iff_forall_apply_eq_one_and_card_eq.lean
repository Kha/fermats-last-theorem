import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Theorems.Thm_CuspidalType_pow_add_one_eq_one_iff_forall_theta_scalarUnit_eq_one
import P2M.Util
namespace P2MW.S_CuspidalType_exists_finset_monoidHom_mem_iff_forall_apply_eq_one_and_card_eq

set_option autoImplicit false

open Polynomial CuspidalType

open Finset

theorem solution (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    ∃ S₀ : Finset ((GaloisField q 2)ˣ →* Kˣ),
      (∀ μ : (GaloisField q 2)ˣ →* Kˣ,
        μ ∈ S₀ ↔ ∀ c : (ZMod q)ˣ, μ (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = 1) ∧
      S₀.card = q + 1 := by
  classical
  haveI : Fintype (GaloisField q 2)ˣ := Fintype.ofFinite _
  haveI : NeZero ((q + 1 : ℕ) : K) := ⟨by exact_mod_cast Nat.succ_ne_zero q⟩
  haveI : Fintype (rootsOfUnity (q + 1) K) := Fintype.ofFinite _

  obtain ⟨β, hβ⟩ := IsCyclic.exists_generator (α := (GaloisField q 2)ˣ)
  have hcardT : Fintype.card (GaloisField q 2)ˣ = q ^ 2 - 1 := by
    rw [Fintype.card_eq_nat_card, Nat.card_units, GaloisField.card q 2 two_ne_zero]
  have hordβ : orderOf β = q ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hβ, ← hcardT, Nat.card_eq_fintype_card]
  have hdvd : q + 1 ∣ orderOf β := ⟨q - 1, by rw [hordβ, ← Nat.sq_sub_sq, one_pow]⟩

  have hgen : ∀ μ ν : (GaloisField q 2)ˣ →* Kˣ, μ β = ν β → μ = ν := by
    intro μ ν h
    refine MonoidHom.ext fun x => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hβ x)
    rw [map_zpow, map_zpow, h]

  have hdiv : ∀ ζ : rootsOfUnity (q + 1) K, orderOf (ζ : Kˣ) ∣ orderOf β := fun ζ =>
    (orderOf_dvd_of_pow_eq_one ((mem_rootsOfUnity _ _).1 ζ.2)).trans hdvd
  let Φ : rootsOfUnity (q + 1) K → ((GaloisField q 2)ˣ →* Kˣ) := fun ζ =>
    monoidHomOfForallMemZpowers hβ (hdiv ζ)
  have hΦ : ∀ ζ, Φ ζ β = (ζ : Kˣ) := fun ζ => monoidHomOfForallMemZpowers_apply_gen hβ (hdiv ζ)
  have hΦinj : Function.Injective Φ := fun ζ ζ' h => Subtype.ext (by rw [← hΦ ζ, ← hΦ ζ', h])
  refine ⟨univ.image Φ, fun μ => ?_, ?_⟩
  · rw [← CuspidalType.pow_add_one_eq_one_iff_forall_theta_scalarUnit_eq_one μ, mem_image]
    constructor
    · rintro ⟨ζ, -, rfl⟩
      refine hgen _ _ ?_
      rw [MonoidHom.pow_apply, hΦ, MonoidHom.one_apply]
      exact (mem_rootsOfUnity _ _).1 ζ.2
    · intro h
      have hζ : μ β ∈ rootsOfUnity (q + 1) K := by
        rw [mem_rootsOfUnity]
        have := DFunLike.congr_fun h β
        rwa [MonoidHom.pow_apply, MonoidHom.one_apply] at this
      exact ⟨⟨μ β, hζ⟩, mem_univ _, hgen _ _ (hΦ _)⟩
  · rw [card_image_of_injective _ hΦinj, card_univ, ← Nat.card_eq_fintype_card,
      HasEnoughRootsOfUnity.natCard_rootsOfUnity]
