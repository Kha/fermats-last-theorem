import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalizedModule_existsUnique_forall_eq_of_span_range_eq_top

set_option autoImplicit false

theorem IsLocalizedModule.existsUnique_forall_eq_of_span_range_eq_top
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [Finite ι] (g : ι → R) (hg : Ideal.span (Set.range g) = ⊤)
    {Mi : ι → Type*} [∀ i, AddCommGroup (Mi i)] [∀ i, Module R (Mi i)]
    (fi : ∀ i, M →ₗ[R] Mi i) [∀ i, IsLocalizedModule (Submonoid.powers (g i)) (fi i)]
    {Mij : ι → ι → Type*} [∀ i j, AddCommGroup (Mij i j)] [∀ i j, Module R (Mij i j)]
    (fij : ∀ i j, M →ₗ[R] Mij i j) [∀ i j, IsLocalizedModule (Submonoid.powers (g i * g j)) (fij i j)]
    (ρ : ∀ i j, Mi i →ₗ[R] Mij i j) (ρ' : ∀ i j, Mi j →ₗ[R] Mij i j)
    (hρ : ∀ i j, (ρ i j).comp (fi i) = fij i j) (hρ' : ∀ i j, (ρ' i j).comp (fi j) = fij i j)
    (m : ∀ i, Mi i) (hm : ∀ i j, ρ i j (m i) = ρ' i j (m j)) :
    ∃! x : M, ∀ i, fi i x = m i := by p2m_exact_reverting @_root_.P2MW.S_IsLocalizedModule_existsUnique_forall_eq_of_span_range_eq_top.solution
