import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_RiemannForm_translation_zero_and_translation_add
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RiemannForm_exists_addSubgroup_mem_iff_nonempty_pullback_translation_iso

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

theorem solution
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (𝓛 : A.Modules) :
    ∃ H : AddSubgroup (L.AlgPoints hc k), ∀ Q : L.AlgPoints hc k,
      Q ∈ H ↔ Nonempty ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛 ≅ 𝓛) := by
  classical

  let T : L.AlgPoints hc k → (A ⟶ A) := fun Q => translation f L (RelativeGroupLaw.AlgPoints.toPoint Q)
  let S : Set (L.AlgPoints hc k) := {Q | Nonempty ((Scheme.Modules.pullback (T Q)).obj 𝓛 ≅ 𝓛)}
  have hT0 : T 0 = 𝟙 A := (AlgebraicGeometry.RiemannForm.translation_zero_and_translation_add k f L hc 0 0).1
  have hTadd : ∀ P Q, T (P + Q) = T P ≫ T Q := fun P Q =>
    (AlgebraicGeometry.RiemannForm.translation_zero_and_translation_add k f L hc P Q).2
  have zero_mem : (0 : L.AlgPoints hc k) ∈ S :=
    ⟨(Scheme.Modules.pullbackCongr hT0).app 𝓛 ≪≫ (Scheme.Modules.pullbackId A).app 𝓛⟩
  have add_mem : ∀ {P Q}, P ∈ S → Q ∈ S → P + Q ∈ S := by
    intro P Q hP hQ
    obtain ⟨eP⟩ := hP
    obtain ⟨eQ⟩ := hQ
    exact ⟨(Scheme.Modules.pullbackCongr (hTadd P Q)).app 𝓛 ≪≫ ((Scheme.Modules.pullbackComp (T P) (T Q)).app 𝓛).symm ≪≫
      (Scheme.Modules.pullback (T P)).mapIso eQ ≪≫ eP⟩
  have neg_mem : ∀ {P}, P ∈ S → -P ∈ S := by
    intro P hP
    obtain ⟨eP⟩ := hP

    have h : T (-P) ≫ T P = 𝟙 A := by rw [← hTadd, neg_add_cancel, hT0]
    exact ⟨(Scheme.Modules.pullback (T (-P))).mapIso eP.symm ≪≫ (Scheme.Modules.pullbackComp (T (-P)) (T P)).app 𝓛 ≪≫
      (Scheme.Modules.pullbackCongr h).app 𝓛 ≪≫ (Scheme.Modules.pullbackId A).app 𝓛⟩
  refine ⟨{ carrier := S, zero_mem' := zero_mem, add_mem' := add_mem, neg_mem' := neg_mem }, fun Q => Iff.rfl⟩
