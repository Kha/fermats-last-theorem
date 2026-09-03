import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_bialgHom_comp_eq_of_bijective_tensorProduct_comul_zmodp

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_bialgHom_comp_eq_of_bijective_tensorProduct_comul_zmodp
    (p : ℕ) [Fact p.Prime] {B : Type v} [CommRing B] [HopfAlgebra (ZMod p) B]
    [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]
    {Bc : Type v} [CommRing Bc] [HopfAlgebra (ZMod p) Bc] [Module.Finite (ZMod p) Bc]
    {Be : Type v} [CommRing Be] [HopfAlgebra (ZMod p) Be] [Module.Finite (ZMod p) Be]
    (qc : B →ₐc[ZMod p] Bc) (πe : B →ₐc[ZMod p] Be) (σ : Be →ₐc[ZMod p] B)
    (Θ : B →ₐc[ZMod p] Bc ⊗[ZMod p] Be)
    (hqc : Function.Surjective qc) (hπe : Function.Surjective πe)
    (hker_πe : RingHom.ker (πe : B →ₐ[ZMod p] Be) = nilradical B)
    (hσ : πe.comp σ = BialgHom.id (ZMod p) Be)
    (hunr : Algebra.FormallyUnramified (ZMod p) Be)
    (hker_qc : RingHom.ker (qc : B →ₐ[ZMod p] Bc) =
      Ideal.map (σ : Be →ₐ[ZMod p] B) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) Be)))
    (hΘ : ∀ b : B, Θ b = Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Bc) (πe : B →ₐ[ZMod p] Be)
      (Coalgebra.comul (R := ZMod p) b))
    (u : B →ₐc[ZMod p] B) :
    ∃ (uc : Bc →ₐc[ZMod p] Bc) (ue : Be →ₐc[ZMod p] Be),
      qc.comp u = uc.comp qc ∧ πe.comp u = ue.comp πe ∧ u.comp σ = σ.comp ue ∧
      ∀ b : B, Θ (u b) = Algebra.TensorProduct.map (uc : Bc →ₐ[ZMod p] Bc) (ue : Be →ₐ[ZMod p] Be) (Θ b) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_bialgHom_comp_eq_of_bijective_tensorProduct_comul_zmodp.solution
