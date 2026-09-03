import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_of_smul_eq
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory NumberField IsDedekindDomain
p2m_open "scoped NumberField.PlaceDecomp NumberField.PlaceTransport~transport_trans_transport~transport_eq_actRingEquiv"

theorem NumberField.PlaceDecomp.exists_conj_and_transport_repHom_of_smul_eq
    (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F]
    (w w₁ : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F) (hσ : σ • w = w₁) :
    Nat.card ↥(NumberField.PlaceDecomp.decomp E F w₁) = Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) ∧
    ∃ (c : ↥(NumberField.PlaceDecomp.decomp E F w₁) →* ↥(NumberField.PlaceDecomp.decomp E F w))
      (T : Rep.res c (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ),
      Function.Bijective c ∧
      (∀ τ : ↥(NumberField.PlaceDecomp.decomp E F w₁), ((c τ : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) = σ⁻¹ * (τ : F ≃ₐ[E] F) * σ) ∧
      (∀ x : (w.adicCompletion F)ˣ, ((Additive.toMul (T.hom (Additive.ofMul x)) : (w₁.adicCompletion F)ˣ) : w₁.adicCompletion F) =
        NumberField.PlaceTransport.transport σ hσ (x : w.adicCompletion F)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_of_smul_eq.solution
