import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceAbove
import P2M.Util
import P2M.Sol.S_NumberField_PlaceTransport_exists_bijective_doubleCoset_decomp_of_under_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open IsDedekindDomain NumberField
p2m_open "scoped NumberField.PlaceTransport~stabilizer_eq_decomp~orbit_eq_setOf_under_eq Pointwise"

theorem NumberField.PlaceTransport.exists_bijective_doubleCoset_decomp_of_under_eq
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (H : Subgroup (F ≃ₐ[E] F)) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v) :
    Finite {v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) // v'.under (𝓞 E) = v} ∧
    ∃ g : {v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) // v'.under (𝓞 E) = v} → (F ≃ₐ[E] F),
      Function.Bijective (fun i => DoubleCoset.mk (NumberField.PlaceDecomp.decomp E F w) H (g i)) ∧
      (∃ i₀, i₀.1 = w.under (𝓞 ↥(IntermediateField.fixedField H)) ∧ g i₀ = 1) ∧
      (∀ i, ((g i)⁻¹ • w).under (𝓞 ↥(IntermediateField.fixedField H)) = i.1) ∧
      (∀ i, ∃ h : ↥H, (h : F ≃ₐ[E] F) • NumberField.PlaceAbove.above (↥(IntermediateField.fixedField H)) F i.1 = (g i)⁻¹ • w) ∧
      (∀ i, Nat.card ↥((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)) =
        Nat.card ↥(H ⊓ NumberField.PlaceDecomp.decomp E F
          (NumberField.PlaceAbove.above (↥(IntermediateField.fixedField H)) F i.1))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceTransport_exists_bijective_doubleCoset_decomp_of_under_eq.solution
