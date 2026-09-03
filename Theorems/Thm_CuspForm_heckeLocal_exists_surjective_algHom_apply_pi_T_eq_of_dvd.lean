import Definitions.Def_CuspForm_HeckeLocal
import P2M.Util
import P2M.Sol.S_CuspForm_heckeLocal_exists_surjective_algHom_apply_pi_T_eq_of_dvd
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat

set_option autoImplicit false

open IsLocalRing

theorem CuspForm.heckeLocal.exists_surjective_algHom_apply_pi_T_eq_of_dvd
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    (S : Set ℕ) (M M' : ℕ) [NeZero M] [NeZero M'] [Fact (CuspForm.HasIntegralStructure M' 2)]
    (hMM' : M ∣ M')
    (hS : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)
    (θ : CuspForm.heckeAlgebra M 2 S →+* ResidueField 𝒪)
    (θ' : CuspForm.heckeAlgebra M' 2 S →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') (hℓS : ℓ ∉ S),
      θ' (CuspForm.heckeAlgebra.T hℓ hℓM' hℓS) =
        θ (CuspForm.heckeAlgebra.T hℓ (fun h => hℓM' (h.trans hMM')) hℓS)) :
    ∃ Ψ : CuspForm.heckeLocal M' S 𝒪 θ' →ₐ[𝒪] CuspForm.heckeLocal M S 𝒪 θ,
      Function.Surjective Ψ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') (hℓS : ℓ ∉ S),
        Ψ (CuspForm.heckeLocal.π M' S 𝒪 θ' (CuspForm.heckeAlgebra.T hℓ hℓM' hℓS)) =
          CuspForm.heckeLocal.π M S 𝒪 θ (CuspForm.heckeAlgebra.T hℓ (fun h => hℓM' (h.trans hMM')) hℓS)) ∧
      (∀ (A : Type) [CommRing A] [Algebra 𝒪 A]
        (f : CuspForm.heckeLocal M S 𝒪 θ →ₐ[𝒪] A) (g : CuspForm.heckeLocal M' S 𝒪 θ' →ₐ[𝒪] A),
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') (hℓS : ℓ ∉ S),
          g (CuspForm.heckeLocal.π M' S 𝒪 θ' (CuspForm.heckeAlgebra.T hℓ hℓM' hℓS)) =
            f (CuspForm.heckeLocal.π M S 𝒪 θ (CuspForm.heckeAlgebra.T hℓ (fun h => hℓM' (h.trans hMM')) hℓS))) →
        g = f.comp Ψ) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeLocal_exists_surjective_algHom_apply_pi_T_eq_of_dvd.solution
