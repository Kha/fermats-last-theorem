import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_ker_uZero_eq_span_of_isEtaSection_of_tangent_eq_neg_mul

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped TensorProduct PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.ker_uZero_eq_span_of_isEtaSection_of_tangent_eq_neg_mul
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ] (ψ : WittVector p k →+* κ)
    (t : Rigidified p Φ κ) (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    (x : PrimeSpectrum κ) (f : κ) (hf : f ∉ x.asIdeal)
    (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
    (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
    (L : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).M →+ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).NMod)
    (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).IsCanonicalLMap L)
    (e : Module.Basis (Fin 2) ℤ_[p] ↥(Q.N₀ x))
    (z₀ z₁ : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).NMod)
    (hz₀ : t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom f) hc hcb hcΦg L hL 0 z₀ ((e 0 : ↥(Q.N₀ x)) : Fin 2 → ℚ_[p]))
    (hz₁ : t.IsEtaSection ι hcΦ rΦ ψ hOD (Rigidified.awayHom f) hc hcb hcΦg L hL 0 z₁ ((e 1 : ↥(Q.N₀ x)) : Fin 2 → ℚ_[p]))
    (m₀ m₁ : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).M)
    (hm₀ : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).vRange.mkQ m₀ = ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).u L hL.isCartierLMap.map_verschiebung ⟨z₀, (AddSubgroup.mem_inf.mp hz₀.1).1⟩)
    (hm₁ : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).vRange.mkQ m₁ = ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom f)) hc).u L hL.isCartierLMap.map_verschiebung ⟨z₁, (AddSubgroup.mem_inf.mp hz₁.1).1⟩)
    (c : κ)
    (htan : ∀ j : Fin 2, MvFormalGroup.CartierModule.tangent m₁ j =
      -(Rigidified.awayHom f c) * MvFormalGroup.CartierModule.tangent m₀ j)
    (hne : ∃ j : Fin 2, MvFormalGroup.CartierModule.tangent m₀ j ≠ 0) :
    LinearMap.ker (Q.u₀ x) = Submodule.span (locRing κ x)
      {algebraMap κ (locRing κ x) c ⊗ₜ[ℤ_[p]] (e 0) + (1 : locRing κ x) ⊗ₜ[ℤ_[p]] (e 1)} := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_ker_uZero_eq_span_of_isEtaSection_of_tangent_eq_neg_mul.solution
