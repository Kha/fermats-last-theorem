import Mathlib
import Definitions.Def_PDivisibleGroup_CharacterDifferential
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff
    {R : Type} [CommRing R] {p h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (S : Type) [CommRing S] [Algebra R S] (v : ℕ) :
    (∀ (ψ : G'.Point S v) (φ : Module.Dual R (G.level v)),
        TensorProduct.rid R S (φ.lTensor S (D.charElem S v ψ)) =
          Point.toAlgHom ψ ((D.toDualEquiv v).symm φ)) ∧
    (∀ (f : G.Point S v) (ψ : G'.Point S v),
        Algebra.TensorProduct.lift (AlgHom.id R S) (Point.toAlgHom f) (fun _ _ => .all _ _)
          (D.charElem S v ψ) = D.pair S v f ψ) ∧
    (∀ ψ ψ' : G'.Point S v, D.charElem S v (ψ * ψ') = D.charElem S v ψ * D.charElem S v ψ') ∧
    D.charElem S v 1 = 1 ∧
    (∀ ψ ψ' : G'.Point S v, D.charDiff S v (ψ * ψ') = D.charDiff S v ψ + D.charDiff S v ψ') ∧
    D.charDiff S v 1 = 0 ∧
    (∀ (S' : Type) [CommRing S'] [Algebra R S'] (σ : S →ₐ[R] S') (ψ : G'.Point S v),
        Algebra.TensorProduct.map σ (AlgHom.id R (G.level v)) (D.charElem S v ψ) =
          D.charElem S' v (G'.pointMap σ v ψ)) ∧
    (∀ (S' : Type) [CommRing S'] [Algebra R S'] (σ : S →ₐ[R] S') (ψ : G'.Point S v),
        TensorProduct.map σ.toLinearMap LinearMap.id (D.charDiff S v ψ) =
          D.charDiff S' v (G'.pointMap σ v ψ)) ∧
    (∀ (ψ : G'.Point S v) (ψ₁ : G'.Point S (v + 1)), G'.pointIncl S v ψ = ψ₁ ^ p →
        (G.transitionAlgHom v).toLinearMap.lTensor S (D.charElem S (v + 1) ψ₁) = D.charElem S v ψ) ∧
    (∀ (ψ : G'.Point S v) (ψ₁ : G'.Point S (v + 1)), G'.pointIncl S v ψ = ψ₁ ^ p →
        (G.cotangentMap v).lTensor S (D.charDiff S (v + 1) ψ₁) = D.charDiff S v ψ) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff.solution
