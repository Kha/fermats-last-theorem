import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_inf_decomp_of_smul_eq
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory NumberField IsDedekindDomain
p2m_open "scoped NumberField.PlaceDecomp NumberField.PlaceTransport~stabilizer_eq_decomp~transport_trans_transport~transport_eq_actRingEquiv"

theorem NumberField.PlaceDecomp.exists_conj_and_transport_repHom_inf_decomp_of_smul_eq
    (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F] (H : Subgroup (F ≃ₐ[E] F))
    (w w₁ : HeightOneSpectrum (𝓞 F)) (h : ↥H) (hh : (h : F ≃ₐ[E] F) • w = w₁) :
    Nat.card ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)) = Nat.card ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w)) ∧
    ∃ (ch : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)) →* ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w)))
      (Th : Rep.res ch (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) ⟶
        Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w₁) ≤ (NumberField.PlaceDecomp.decomp E F w₁)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ)),
      Function.Bijective ch ∧
      (∀ x : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)),
        ((ch x : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w))) : F ≃ₐ[E] F) = (h : F ≃ₐ[E] F)⁻¹ * (x : F ≃ₐ[E] F) * (h : F ≃ₐ[E] F)) ∧
      (∀ x : (w.adicCompletion F)ˣ, ((Additive.toMul (Th.hom (Additive.ofMul x)) : (w₁.adicCompletion F)ˣ) : w₁.adicCompletion F) =
        NumberField.PlaceTransport.transport (h : F ≃ₐ[E] F) hh (x : w.adicCompletion F)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_inf_decomp_of_smul_eq.solution
