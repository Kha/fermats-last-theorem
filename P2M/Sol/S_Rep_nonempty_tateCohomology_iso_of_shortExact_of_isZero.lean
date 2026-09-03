import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Theorems.Thm_Rep_exact_tateHneg1Map_tateDeltaNeg1
import Theorems.Thm_Rep_exact_tateDeltaNeg1_tateH0Map
import Theorems.Thm_Rep_exact_tateH0Map_tateDelta0
import Theorems.Thm_Rep_exact_tateDelta0_map
import Theorems.Thm_Rep_exact_tateDeltaNeg2_tateHneg1Map
import Theorems.Thm_Rep_exact_map_tateDeltaNeg2
import P2M.Util
namespace P2MW.S_Rep_nonempty_tateCohomology_iso_of_shortExact_of_isZero

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep P2MW.S_Rep_nonempty_tateCohomology_iso_of_shortExact_of_isZero.Rep"

namespace Rep
p2m_export "Rep" "of tateCohomology tateδneg1 tateδ₀ tateδneg2 exact_tateHneg1Map_tateDeltaNeg1 exact_tateDeltaNeg1_tateH0Map exact_tateH0Map_tateDelta0 exact_tateDelta0_map exact_tateDeltaNeg2_tateHneg1Map exact_map_tateDeltaNeg2"
namespace DimShiftAux
p2m_open "Rep"

variable {k : Type u} [CommRing k]

lemma eq_zero_of_isZero {M : ModuleCat.{u} k} (h : CategoryTheory.Limits.IsZero M) (x : M) : x = 0 := by
  have := congrArg (fun φ : M ⟶ M => φ.hom x) (h.eq_of_src (𝟙 M) 0)
  simpa using this

lemma injective_of_exact {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module k M] [Module k N] [Module k P] {f : M →ₗ[k] N} {g : N →ₗ[k] P}
    (h : Function.Exact f g) (hM : ∀ x : M, x = 0) : Function.Injective g := by
  intro a b hab
  obtain ⟨c, hc⟩ := (h (a - b)).1 (by rw [map_sub, hab, sub_self])
  rw [hM c, map_zero] at hc
  exact sub_eq_zero.1 hc.symm

lemma surjective_of_exact {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module k M] [Module k N] [Module k P] {f : M →ₗ[k] N} {g : N →ₗ[k] P}
    (h : Function.Exact f g) (hP : ∀ y : P, y = 0) : Function.Surjective f :=
  fun y => (h y).1 (hP _)

end Rep.DimShiftAux

theorem solution
    {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (q : ℤ)
    (h₂ : CategoryTheory.Limits.IsZero (X.X₂.tateCohomology q))
    (h₂' : CategoryTheory.Limits.IsZero (X.X₂.tateCohomology (q + 1))) :
    Nonempty (X.X₃.tateCohomology q ≅ X.X₁.tateCohomology (q + 1)) := by
  rcases q with (_ | n) | (_ | _ | n)
  ·
    have hinj : Function.Injective (Rep.tateδ₀ hX) :=
      Rep.DimShiftAux.injective_of_exact (Rep.exact_tateH0Map_tateDelta0 hX) (Rep.DimShiftAux.eq_zero_of_isZero h₂)
    have hsurj : Function.Surjective (Rep.tateδ₀ hX) :=
      Rep.DimShiftAux.surjective_of_exact (Rep.exact_tateDelta0_map hX) (Rep.DimShiftAux.eq_zero_of_isZero h₂')
    exact ⟨(LinearEquiv.ofBijective (Rep.tateδ₀ hX) ⟨hinj, hsurj⟩).toModuleIso⟩
  ·
    show Nonempty (groupCohomology X.X₃ (n + 1) ≅ groupCohomology X.X₁ (n + 1 + 1))
    haveI := groupCohomology.isIso_δ_of_isZero hX (n + 1) h₂ h₂'
    exact ⟨CategoryTheory.asIso (groupCohomology.δ hX (n + 1) (n + 1 + 1) rfl)⟩
  ·
    have hinj : Function.Injective (Rep.tateδneg1 hX) :=
      Rep.DimShiftAux.injective_of_exact (Rep.exact_tateHneg1Map_tateDeltaNeg1 hX) (Rep.DimShiftAux.eq_zero_of_isZero h₂)
    have hsurj : Function.Surjective (Rep.tateδneg1 hX) :=
      Rep.DimShiftAux.surjective_of_exact (Rep.exact_tateDeltaNeg1_tateH0Map hX) (Rep.DimShiftAux.eq_zero_of_isZero h₂')
    exact ⟨(LinearEquiv.ofBijective (Rep.tateδneg1 hX) ⟨hinj, hsurj⟩).toModuleIso⟩
  ·
    have hinj : Function.Injective (Rep.tateδneg2 hX) :=
      Rep.DimShiftAux.injective_of_exact (Rep.exact_map_tateDeltaNeg2 hX) (Rep.DimShiftAux.eq_zero_of_isZero h₂)
    have hsurj : Function.Surjective (Rep.tateδneg2 hX) :=
      Rep.DimShiftAux.surjective_of_exact (Rep.exact_tateDeltaNeg2_tateHneg1Map hX) (Rep.DimShiftAux.eq_zero_of_isZero h₂')
    exact ⟨(LinearEquiv.ofBijective (Rep.tateδneg2 hX) ⟨hinj, hsurj⟩).toModuleIso⟩
  ·
    show Nonempty (groupHomology X.X₃ (n + 1 + 1) ≅ groupHomology X.X₁ (n + 1))
    haveI := groupHomology.isIso_δ_of_isZero hX (n + 1) h₂ h₂'
    exact ⟨CategoryTheory.asIso (groupHomology.δ hX (n + 1 + 1) (n + 1) rfl)⟩
