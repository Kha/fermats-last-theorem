import Mathlib
import P2M.Util
import P2M.Sol.S_MeromorphicAt_exists_meromorphicOrderAt_neg_of_prod_eventuallyEq_mul_prod

theorem MeromorphicAt.exists_meromorphicOrderAt_neg_of_prod_eventuallyEq_mul_prod
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι κ : Type*}
    {s : Finset ι} {t : Finset κ} {f : ι → 𝕜 → 𝕜} {p : 𝕜 → 𝕜} {h : κ → 𝕜 → 𝕜} {x : 𝕜}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x)
    (hp : MeromorphicAt p x) (hpole : meromorphicOrderAt p x < 0)
    (hh : ∀ j ∈ t, AnalyticAt 𝕜 (h j) x) (hh0 : ∀ j ∈ t, h j x ≠ 0)
    (hfg : ∀ᶠ z in nhdsWithin x {x}ᶜ, (∏ i ∈ s, f i z) = p z * ∏ j ∈ t, h j z) :
    ∃ i ∈ s, meromorphicOrderAt (f i) x < 0 := by p2m_exact_reverting @_root_.P2MW.S_MeromorphicAt_exists_meromorphicOrderAt_neg_of_prod_eventuallyEq_mul_prod.solution
