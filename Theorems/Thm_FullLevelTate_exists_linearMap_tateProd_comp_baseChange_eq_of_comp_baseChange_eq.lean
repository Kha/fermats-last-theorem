import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_TateRep
import P2M.Util
import P2M.Sol.S_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_of_comp_baseChange_eq

set_option autoImplicit false

open scoped TensorProduct

theorem FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_of_comp_baseChange_eq
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime] (O' : Type) [CommRing O'] [Algebra ℤ_[lam] O']
    (R : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Module.End O' (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')))
    (hR : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : O')
      (x : TateModule lam (ModularCurve.FullLevel.Jac q M')),
      R σ (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] ModularCurve.FullLevel.tateGal q M' lam σ x)
    (G : CuspidalType.GL2 q →* Module.End O' (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')))
    (hG : ∀ (g : CuspidalType.GL2 q) (a : O') (x : TateModule lam (ModularCurve.FullLevel.Jac q M')),
      G g (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] ModularCurve.FullLevel.tateGL2 q M' lam g x)
    (K : Type) [Field K] [Algebra O' K] [Algebra ℚ_[lam] K]
    (hOK : ∀ z : ℤ_[lam], algebraMap O' K (algebraMap ℤ_[lam] O' z) = algebraMap ℚ_[lam] K (z : ℚ_[lam]))
    (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (DrinfeldCurve.CoordRing q k)] (index : Type)
    (sp₀ : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M') →ₗ[ℚ_[lam]]
      DrinfeldCurve.tateProd q k lam ℚ_[lam] index) :
    ∃ sp : K ⊗[O'] (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')) →ₗ[K]
        DrinfeldCurve.tateProd q k lam K index,
      (∀ (c : K) (a : O') (x : TateModule lam (ModularCurve.FullLevel.Jac q M')) (i : index),
        sp (c ⊗ₜ[O'] (a ⊗ₜ[ℤ_[lam]] x)) i =
          (algebraMap O' K a * c) ⊗ₜ[ℚ_[lam]] TensorProduct.lid ℚ_[lam] _ (sp₀ ((1 : ℚ_[lam]) ⊗ₜ[ℤ_[lam]] x) i)) ∧
      ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (g : CuspidalType.GL2 q) (α : (GaloisField q 2)ˣ)
          (hg : (g, α) ∈ DrinfeldCurve.hSubgroup q),
        sp₀ ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam g * ModularCurve.FullLevel.tateGal q M' lam τ).baseChange
              ℚ_[lam] = DrinfeldCurve.tateProdRep q k lam ℚ_[lam] index ⟨(g, α), hg⟩ ∘ₗ sp₀ →
          sp ∘ₗ ((G g * R τ).baseChange K) = DrinfeldCurve.tateProdRep q k lam K index ⟨(g, α), hg⟩ ∘ₗ sp := by p2m_exact_reverting @_root_.P2MW.S_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_of_comp_baseChange_eq.solution
