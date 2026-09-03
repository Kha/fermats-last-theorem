import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_HeckeProj
import Theorems.Thm_ModularCurve_heckeProj_surjective
import Theorems.Thm_ModularCurve_exists_sub_C_mem_eisensteinIdeal
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import P2M.Util
namespace P2MW.S_CuspForm_exists_ringHom_zmod_of_eisenstein_injective
open ModularCurve

namespace S09RC

private theorem exists_ringHom_zmod (m : ℕ) {T : Type*} [CommRing T] (I : Ideal T)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk I).comp (algebraMap ℤ T)))
    (hdvd : ∀ c : ℤ, algebraMap ℤ T c ∈ I → (m : ℤ) ∣ c) :
    ∃ χ : T →+* ZMod m, (∀ i ∈ I, χ i = 0) ∧ ∀ c : ℤ, χ (algebraMap ℤ T c) = (c : ZMod m) := by
  have hker : ∀ a : ℤ, a ∈ RingHom.ker ((Ideal.Quotient.mk I).comp (algebraMap ℤ T)) →
      Int.castRingHom (ZMod m) a = 0 := by
    intro a ha
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at ha
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd a m).mpr (hdvd a ha)
  set χ : T →+* ZMod m :=
    ((Ideal.Quotient.lift _ (Int.castRingHom (ZMod m)) hker).comp
      (RingHom.quotientKerEquivOfSurjective hsurj).symm.toRingHom).comp
      (Ideal.Quotient.mk I) with hχ
  refine ⟨χ, ?_, ?_⟩
  · intro i hi
    have h0 : Ideal.Quotient.mk I i = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hi
    rw [hχ, RingHom.comp_apply, RingHom.comp_apply, h0, map_zero, map_zero]
  · intro c
    exact eq_intCast (χ.comp (algebraMap ℤ T)) c

private theorem surjective_intComp (p m : ℕ) [NeZero p] :
    Function.Surjective ((Ideal.Quotient.mk
        (Ideal.map (heckeProj p) (eisensteinIdeal p) ⊔
          Ideal.span {((m : ℕ) : CuspForm.heckeAlgebra p 2 ∅)})).comp
      (algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅))) := by
  set J : Ideal (CuspForm.heckeAlgebra p 2 ∅) :=
    Ideal.map (heckeProj p) (eisensteinIdeal p) ⊔
      Ideal.span {((m : ℕ) : CuspForm.heckeAlgebra p 2 ∅)} with hJ
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨t, rfl⟩ := ModularCurve.heckeProj_surjective p a
  obtain ⟨n, hn⟩ := ModularCurve.exists_sub_C_mem_eisensteinIdeal p t
  have h2 := Ideal.mem_map_of_mem (heckeProj p) hn
  rw [map_sub, heckeProj_C] at h2
  refine ⟨n, ?_⟩
  show Ideal.Quotient.mk J (algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅) n) =
    Ideal.Quotient.mk J (heckeProj p t)
  symm
  rw [Ideal.Quotient.eq, hJ]
  exact Submodule.mem_sup_left h2

end S09RC

namespace CuspForm p2m_export "CuspForm" "mk heckeAlgebra" end CuspForm
p2m_open_scoped "CuspForm" in
private theorem CuspForm.exists_ringHom_zmod_of_eisenstein_injective (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (hinj : ∀ c : ℤ, algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅) c ∈ Ideal.map (heckeProj p) (eisensteinIdeal p) ⊔ Ideal.span {((m : ℕ) : CuspForm.heckeAlgebra p 2 ∅)} → (m : ℤ) ∣ c) : ∃ χ : CuspForm.heckeAlgebra p 2 ∅ →+* ZMod m, (∀ i ∈ Ideal.map (heckeProj p) (eisensteinIdeal p), χ i = 0) ∧ ∀ c : ℤ, χ (algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅) c) = (c : ZMod m) := by

  have _ := hm
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨χ, hkill, hcast⟩ :=
    S09RC.exists_ringHom_zmod m _ (S09RC.surjective_intComp p m) hinj
  exact ⟨χ, fun i hi => hkill i (Submodule.mem_sup_left hi), hcast⟩

open ModularCurve in
theorem solution : ∀ (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (hinj : ∀ c : ℤ, algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅) c ∈ Ideal.map (heckeProj p) (eisensteinIdeal p) ⊔ Ideal.span {((m : ℕ) : CuspForm.heckeAlgebra p 2 ∅)} → (m : ℤ) ∣ c), ∃ χ : CuspForm.heckeAlgebra p 2 ∅ →+* ZMod m, (∀ i ∈ Ideal.map (heckeProj p) (eisensteinIdeal p), χ i = 0) ∧ ∀ c : ℤ, χ (algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅) c) = (c : ZMod m) :=
  @CuspForm.exists_ringHom_zmod_of_eisenstein_injective
