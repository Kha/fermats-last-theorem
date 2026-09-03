import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_uniformizing_separating_form

set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.Place.exists_uniformizing_separating_form
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (v : Place k F) {j : F} {n : ℕ} (β : Fin n → F)
    (cv : k) (hcv : 0 < v.ord (j - algebraMap k F cv))
    (βv : Fin n → k)
    (hβv : ∀ i, β i = algebraMap k F (βv i) ∨ 0 < v.ord (β i - algebraMap k F (βv i)))
    (hU1 : v.ord (j - algebraMap k F cv) = 1 ∨ ∃ i, v.ord (β i - algebraMap k F (βv i)) = 1)
    {r : ℕ} (pt : Fin r → Place k F) (cpt : Fin r → k) (βpt : Fin r → Fin n → k)
    (hS1 : ∀ t, pt t ≠ v → cpt t ≠ cv ∨ βpt t ≠ βv)
    {a : ℕ} (θ : Fin a → k) (hθ : Function.Injective θ) (ha : n * (r + 1) < a) :
    ∃ s : Fin a,
      v.ord ((j + ∑ i : Fin n, algebraMap k F (θ s ^ (i.val + 1)) * β i)
          - algebraMap k F (cv + ∑ i : Fin n, θ s ^ (i.val + 1) * βv i)) = 1 ∧
      ∀ t, pt t ≠ v →
        cpt t + ∑ i : Fin n, θ s ^ (i.val + 1) * βpt t i
          ≠ cv + ∑ i : Fin n, θ s ^ (i.val + 1) * βv i := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_uniformizing_separating_form.solution
