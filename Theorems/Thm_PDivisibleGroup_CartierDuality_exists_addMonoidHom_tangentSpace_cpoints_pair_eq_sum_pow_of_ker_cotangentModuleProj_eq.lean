import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_CharacterDifferential
import Definitions.Def_PDivisibleGroup_CompletedPoints
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq

set_option autoImplicit false

open scoped TensorProduct in

theorem PDivisibleGroup.CartierDuality.exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [Algebra ℤ_[p] R]
    (htf : ∀ x : R, (p : R) * x = 0 → x = 0)
    (hsep : ∀ x : R, (∀ i : ℕ, x ∈ Ideal.span {(p : R) ^ i}) → x = 0)
    {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (hsurj : ∀ v, Function.Surjective (G.cotangentModuleProj v))
    (hker : ∀ v, LinearMap.ker (G.cotangentModuleProj v) =
      Ideal.span {(p : R) ^ v} • (⊤ : Submodule R G.cotangentModule)) :
    ∃ (m : ℕ) (c : ℕ → R) (e : G.tangentSpace R →+ G.CPoints R),
      (∀ k : ℕ, (k.factorial : R) * c k = (p : R) ^ (m * k)) ∧
      Function.Injective e ∧
      ∀ (S : Type) [CommRing S] [Algebra R S] (τ : G.tangentSpace R) (i w : ℕ), i ≤ w →
        ∀ (f : G.Point (S ⧸ Ideal.span {(p : S) ^ i}) w),
          G.pointsMkAdd _ w (Additive.ofMul f) =
            G.cpointsProj S i (G.cpointsMap (Algebra.ofId R S) (e τ)) →
        ∀ (ψ : G'.Point S w) (z : S ⊗[R] G.cotangentModule),
          (G.cotangentModuleProj w).lTensor S z = D.charDiff S w ψ →
          D.pair _ w f (G'.pointMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : S) ^ i})) w ψ) =
            ∑ k ∈ Finset.range i,
              algebraMap R _ (c k) *
                (Ideal.Quotient.mk (Ideal.span {(p : S) ^ i})
                  (TensorProduct.rid R S (τ.lTensor S z))) ^ k := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq.solution
