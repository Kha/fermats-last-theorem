import Mathlib
import P2M.Util
import P2M.Sol.S_Module_End_exists_eigenvector_or_exists_eigenvector_of_dualMap_comp_eq_smul

set_option autoImplicit false

theorem Module.End.exists_eigenvector_or_exists_eigenvector_of_dualMap_comp_eq_smul
    {K : Type*} [Field K]
    {L S Ω' : Type*} [AddCommGroup L] [Module K L] [AddCommGroup S] [Module K S] [AddCommGroup Ω'] [Module K Ω']
    [FiniteDimensional K L] [FiniteDimensional K Ω']
    {ι : Type*}
    (TL : ι → Module.End K L) (hTL : ∀ i j, Commute (TL i) (TL j))
    (TS : ι → Module.End K S)
    (TΩ : ι → Module.End K Ω') (hTΩ : ∀ i j, Commute (TΩ i) (TΩ j))
    (res : L →ₗ[K] S) (hres : ∀ i, res ∘ₗ TL i = TS i ∘ₗ res)
    (Θ : S →ₗ[K] Module.Dual K Ω') (hexact : ∀ v : S, Θ v = 0 ↔ v ∈ LinearMap.range res)
    (c : ι → K) (hc : ∀ i, c i ≠ 0)
    (hΘ : ∀ (i : ι) (v : S), Θ (TS i v) = c i • (TΩ i).dualMap (Θ v))
    (lam : ι → K) (v : S) (hv0 : v ≠ 0) (hv : ∀ i, TS i v = lam i • v) :
    (∃ G : L, G ≠ 0 ∧ ∀ i, TL i G = lam i • G) ∨
    (∃ ω : Ω', ω ≠ 0 ∧ ∀ i, TΩ i ω = ((c i)⁻¹ * lam i) • ω) := by p2m_exact_reverting @_root_.P2MW.S_Module_End_exists_eigenvector_or_exists_eigenvector_of_dualMap_comp_eq_smul.solution
