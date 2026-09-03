import Mathlib
import Definitions.Def_PDivisibleGroup_CharacterDifferential
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_apply_eq_charDiff

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.exists_addMonoidHom_tateModule_apply_eq_charDiff
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] {G G' : PDivisibleGroup R p h}
    (D : G.CartierDuality G') (S : Type) [CommRing S] [Algebra R S] :
    ∃ HT : TateModule p (G'.Points S) →+ ((v : ℕ) → TensorProduct R S (G.Cotangent v)),
      (∀ (y : TateModule p (G'.Points S)) (v : ℕ) (ψ : G'.Point S v),
          G'.pointsMkAdd S v (Additive.ofMul ψ) = (y : ℕ → G'.Points S) v →
            HT y v = D.charDiff S v ψ) ∧
      (∀ (y : TateModule p (G'.Points S)) (v : ℕ),
          (G.cotangentMap v).lTensor S (HT y (v + 1)) = HT y v) ∧
      (∀ (a : ℤ_[p]) (y : TateModule p (G'.Points S)) (v : ℕ), HT (a • y) v = a.appr v • HT y v) ∧
      (∀ (σ : S ≃ₐ[R] S) (y : TateModule p (G'.Points S)) (v : ℕ),
          HT (G'.tateModuleRep S σ y) v =
            TensorProduct.map (σ : S →ₐ[R] S).toLinearMap LinearMap.id (HT y v)) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_apply_eq_charDiff.solution
