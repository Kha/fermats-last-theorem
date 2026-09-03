import Mathlib
import P2M.Util
import P2M.Sol.S_AdjoinRoot_exists_monoidHom_algEquiv_bijective_tensorProduct_cyclotomic_of_isUnit

set_option autoImplicit false

open Polynomial TensorProduct

universe u

theorem AdjoinRoot.exists_monoidHom_algEquiv_bijective_tensorProduct_cyclotomic_of_isUnit
    (𝒪 : Type u) [CommRing 𝒪] (m : ℕ) (hm : IsUnit ((m : ℕ) : 𝒪)) :
    ∃ τ : (ZMod m)ˣ →* (AdjoinRoot (cyclotomic m 𝒪) ≃ₐ[𝒪] AdjoinRoot (cyclotomic m 𝒪)),
      (∀ a : (ZMod m)ˣ, τ a (AdjoinRoot.root (cyclotomic m 𝒪)) = AdjoinRoot.root (cyclotomic m 𝒪) ^ (a : ZMod m).val) ∧
      Function.Bijective fun x : AdjoinRoot (cyclotomic m 𝒪) ⊗[𝒪] AdjoinRoot (cyclotomic m 𝒪) => fun σ : (ZMod m)ˣ =>
        Algebra.TensorProduct.lmul' (S := AdjoinRoot (cyclotomic m 𝒪)) 𝒪
          (Algebra.TensorProduct.map (AlgHom.id 𝒪 (AdjoinRoot (cyclotomic m 𝒪)))
            ((τ σ : AdjoinRoot (cyclotomic m 𝒪) ≃ₐ[𝒪] AdjoinRoot (cyclotomic m 𝒪)) :
              AdjoinRoot (cyclotomic m 𝒪) →ₐ[𝒪] AdjoinRoot (cyclotomic m 𝒪)) x) := by p2m_exact_reverting @_root_.P2MW.S_AdjoinRoot_exists_monoidHom_algEquiv_bijective_tensorProduct_cyclotomic_of_isUnit.solution
