import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self_of_field
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self_of_field
    {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
    {h : ℕ} (H : PDivisibleGroup F p h)
    (ε ε' : ∀ v : ℕ, H.level v →ₐc[F] H.level v)
    (hε : ∀ v, (ε v).comp (ε v) = ε v) (hε' : ∀ v, (ε' v).comp (ε' v) = ε' v)
    (hεε' : ∀ v, (ε v : H.level v →ₐ[F] H.level v).comp (ε' v : H.level v →ₐ[F] H.level v) =
      (Algebra.ofId F (H.level v)).comp (Bialgebra.counitAlgHom F (H.level v)))
    (hε'ε : ∀ v, (ε' v : H.level v →ₐ[F] H.level v).comp (ε v : H.level v →ₐ[F] H.level v) =
      (Algebra.ofId F (H.level v)).comp (Bialgebra.counitAlgHom F (H.level v)))
    (hsum : ∀ v, WithConv.toConv (ε v : H.level v →ₐ[F] H.level v) *
        WithConv.toConv (ε' v : H.level v →ₐ[F] H.level v) =
      WithConv.toConv (AlgHom.id F (H.level v)))
    (hεt : ∀ v, (H.transition v).comp (ε (v + 1)) = (ε v).comp (H.transition v))
    (hε't : ∀ v, (H.transition v).comp (ε' (v + 1)) = (ε' v).comp (H.transition v)) :
    ∃ (h₁ h₂ : ℕ), h₁ + h₂ = h ∧
    ∃ (H₁ : PDivisibleGroup F p h₁) (H₂ : PDivisibleGroup F p h₂)
      (π₁ : ∀ v, H.level v →ₐc[F] H₁.level v) (π₂ : ∀ v, H.level v →ₐc[F] H₂.level v)
      (σ₁ : ∀ v, H₁.level v →ₐ[F] H.level v) (σ₂ : ∀ v, H₂.level v →ₐ[F] H.level v)
      (Θ : ∀ v, H.level v →ₐc[F] H₁.level v ⊗[F] H₂.level v),
      (∀ v, Function.Surjective (π₁ v)) ∧ (∀ v, Function.Surjective (π₂ v)) ∧
      (∀ v, (π₁ v).comp (H.transition v) = (H₁.transition v).comp (π₁ (v + 1))) ∧
      (∀ v, (π₂ v).comp (H.transition v) = (H₂.transition v).comp (π₂ (v + 1))) ∧
      (∀ v, (π₁ v : H.level v →ₐ[F] H₁.level v).comp (σ₁ v) = AlgHom.id F (H₁.level v)) ∧
      (∀ v, (σ₁ v).comp (π₁ v : H.level v →ₐ[F] H₁.level v) = (ε v : H.level v →ₐ[F] H.level v)) ∧
      (∀ v, (π₂ v : H.level v →ₐ[F] H₂.level v).comp (σ₂ v) = AlgHom.id F (H₂.level v)) ∧
      (∀ v, (σ₂ v).comp (π₂ v : H.level v →ₐ[F] H₂.level v) = (ε' v : H.level v →ₐ[F] H.level v)) ∧
      (∀ v, Function.Bijective (Θ v)) ∧
      (∀ v b, Θ v b = Algebra.TensorProduct.map (π₁ v : H.level v →ₐ[F] H₁.level v)
        (π₂ v : H.level v →ₐ[F] H₂.level v) (Coalgebra.comul (R := F) b)) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self_of_field.solution
