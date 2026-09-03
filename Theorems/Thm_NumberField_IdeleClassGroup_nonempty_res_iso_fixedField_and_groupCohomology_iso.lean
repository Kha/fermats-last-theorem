import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import P2M.Util
import P2M.Sol.S_NumberField_IdeleClassGroup_nonempty_res_iso_fixedField_and_groupCohomology_iso

set_option autoImplicit false
open NumberField M4aHerbrand CategoryTheory

theorem NumberField.IdeleClassGroup.nonempty_res_iso_fixedField_and_groupCohomology_iso
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (S : Subgroup (F ≃ₐ[E] F))
    (D' : IdeleGaloisDescent (𝓞 F) (IntermediateField.fixedField S) F)
    [MulDistribMulAction (F ≃ₐ[IntermediateField.fixedField S] F) (IdeleClassGroup (𝓞 F) F)]
    (hact' : ∀ (g : F ≃ₐ[IntermediateField.fixedField S] F) (c : IdeleClassGroup (𝓞 F) F),
      g • c = D'.classAct g c)
    (ι : S ≃* (F ≃ₐ[IntermediateField.fixedField S] F))
    (hι : ∀ (s : S) (x : F), ι s x = (s : F ≃ₐ[E] F) x) :
    Nonempty (Rep.res S.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ≅
        Rep.res ι.toMonoidHom (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField S] F)
          (IdeleClassGroup (𝓞 F) F))) ∧
      ∀ n : ℕ, Nonempty (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) n ≅
        groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField S] F)
          (IdeleClassGroup (𝓞 F) F)) n) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_IdeleClassGroup_nonempty_res_iso_fixedField_and_groupCohomology_iso.solution
