import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import P2M.Util
import P2M.Sol.S_M4aHerbrand_unitIdelesTrivialOn_nonempty_res_iso_fixedField_and_groupCohomology_iso

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand CategoryTheory
theorem M4aHerbrand.unitIdelesTrivialOn.nonempty_res_iso_fixedField_and_groupCohomology_iso
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F) (T : Set (HeightOneSpectrum (𝓞 F)))
    [MulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T)]
    (hactU : ∀ (g : F ≃ₐ[E] F) (x : unitIdelesTrivialOn (𝓞 F) F T),
      ((g • x : unitIdelesTrivialOn (𝓞 F) F T) : (AdeleRing (𝓞 F) F)ˣ) = D.unitsAct g x)
    (H : Type) [Group H] (f : H →* (F ≃ₐ[E] F))
    (D' : IdeleGaloisDescent (𝓞 F) (IntermediateField.fixedField f.range) F)
    [MulDistribMulAction (F ≃ₐ[IntermediateField.fixedField f.range] F) (unitIdelesTrivialOn (𝓞 F) F T)]
    (hactU' : ∀ (g : F ≃ₐ[IntermediateField.fixedField f.range] F) (x : unitIdelesTrivialOn (𝓞 F) F T),
      ((g • x : unitIdelesTrivialOn (𝓞 F) F T) : (AdeleRing (𝓞 F) F)ˣ) = D'.unitsAct g x)
    (ι : H ≃* (F ≃ₐ[IntermediateField.fixedField f.range] F))
    (hι : ∀ (h : H) (x : F), ι h x = f h x) :
    Nonempty (Rep.res f (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T)) ≅
        Rep.res ι.toMonoidHom (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField f.range] F)
          (unitIdelesTrivialOn (𝓞 F) F T))) ∧
      ∀ n : ℕ, Nonempty (groupCohomology (Rep.res f
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T))) n ≅
        groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField f.range] F)
          (unitIdelesTrivialOn (𝓞 F) F T)) n) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_unitIdelesTrivialOn_nonempty_res_iso_fixedField_and_groupCohomology_iso.solution
