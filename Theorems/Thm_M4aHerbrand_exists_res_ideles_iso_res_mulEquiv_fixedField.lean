import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import P2M.Util
import P2M.Sol.S_M4aHerbrand_exists_res_ideles_iso_res_mulEquiv_fixedField

set_option autoImplicit false
open NumberField M4aHerbrand CategoryTheory

theorem M4aHerbrand.exists_res_ideles_iso_res_mulEquiv_fixedField
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : F ≃ₐ[E] F) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (S : Subgroup (F ≃ₐ[E] F))
    (D' : IdeleGaloisDescent (𝓞 F) (IntermediateField.fixedField S) F)
    [MulDistribMulAction (F ≃ₐ[IntermediateField.fixedField S] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI' : ∀ (g : F ≃ₐ[IntermediateField.fixedField S] F) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D'.unitsAct g x)
    (ι : S ≃* (F ≃ₐ[IntermediateField.fixedField S] F))
    (hι : ∀ (s : S) (x : F), ι s x = (s : F ≃ₐ[E] F) x) :
    ∃ e : Rep.res S.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ≅
        Rep.res ι.toMonoidHom (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField S] F) (AdeleRing (𝓞 F) F)ˣ),
      (∀ x, e.hom.hom x = x) ∧ (∀ x, e.inv.hom x = x) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_exists_res_ideles_iso_res_mulEquiv_fixedField.solution
