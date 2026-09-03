import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_PlaceDecomp_exists_conj_subgroupOf_and_transport_repHom_of_smul_eq
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory NumberField IsDedekindDomain
p2m_open "scoped NumberField.PlaceDecomp NumberField.PlaceTransport~stabilizer_eq_decomp~transport_trans_transport~transport_eq_actRingEquiv"
open scoped Pointwise

theorem NumberField.PlaceDecomp.exists_conj_subgroupOf_and_transport_repHom_of_smul_eq
    (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F] (H : Subgroup (F ≃ₐ[E] F))
    (w w₁ : HeightOneSpectrum (𝓞 F)) (g : F ≃ₐ[E] F) (hg : g • w₁ = w) :
    Nat.card ↥((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)) = Nat.card ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)) ∧
    ∃ (c'' : ↥((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)) →* ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)))
      (T'' : Rep.res c'' (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w₁) ≤ (NumberField.PlaceDecomp.decomp E F w₁)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ)) ⟶
        Rep.res ((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)).subtype
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)),
      Function.Bijective c'' ∧
      (∀ x : ↥((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)),
        ((c'' x : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁))) : F ≃ₐ[E] F) = g⁻¹ * ((x : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) * g) ∧
      (∀ x : (w₁.adicCompletion F)ˣ, ((Additive.toMul (T''.hom (Additive.ofMul x)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) =
        NumberField.PlaceTransport.transport g hg (x : w₁.adicCompletion F)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_exists_conj_subgroupOf_and_transport_repHom_of_smul_eq.solution
