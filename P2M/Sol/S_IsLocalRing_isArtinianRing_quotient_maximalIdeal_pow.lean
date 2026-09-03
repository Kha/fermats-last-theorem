import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import P2M.Util
namespace P2MW.S_IsLocalRing_isArtinianRing_quotient_maximalIdeal_pow

open IsLocalRing

namespace LCMazurS10LTART

variable {A : Type*} [CommRing A] [IsLocalRing A]

omit [IsLocalRing A] in
theorem nontrivial_quotient_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) : Nontrivial (A ⧸ I) :=
  Ideal.Quotient.nontrivial_iff.mpr hI

theorem isLocalRing_quotient_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) : IsLocalRing (A ⧸ I) :=
  haveI := nontrivial_quotient_of_ne_top hI
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem isLocalHom_mk_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) : IsLocalHom (Ideal.Quotient.mk I) :=
  haveI := nontrivial_quotient_of_ne_top hI
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

theorem map_maximalIdeal_mk_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) [IsLocalRing (A ⧸ I)] :
    (maximalIdeal A).map (Ideal.Quotient.mk I) = maximalIdeal (A ⧸ I) := by
  haveI := isLocalHom_mk_of_ne_top hI
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr (le_maximalIdeal hI), mem_maximalIdeal,
    mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]

end LCMazurS10LTART

open LCMazurS10LTART in
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (m : ℕ) :
    IsArtinianRing (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) := by
  have hne : IsLocalRing.maximalIdeal A ^ (m + 1) ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ Ideal.pow_le_self m.succ_ne_zero))
  haveI := isLocalRing_quotient_of_ne_top hne
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal, ← map_maximalIdeal_mk_of_ne_top hne]
  exact ⟨m + 1, by rw [← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker,
    Ideal.mk_ker]⟩
