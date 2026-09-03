import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_isBaseChange_ker_span_range_eq_top_of_flat

set_option autoImplicit false

universe u v

theorem LinearMap.exists_isBaseChange_ker_span_range_eq_top_of_flat
    {B : Type u} [CommRing B] {B' : Type u} [CommRing B'] [Algebra B B'] [Module.Flat B B']
    {M : Type v} [AddCommGroup M] [Module B M]
    {M' : Type v} [AddCommGroup M'] [Module B M'] [Module B' M'] [IsScalarTower B B' M']
    (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M)
    (p' : (Fin r → B') →ₗ[B'] M') (hp' : ∀ v : Fin r → B, p' (fun i => algebraMap B B' (v i)) = μ (p v)) :
    ∃ g : ↥(LinearMap.ker p) →ₗ[B] ↥(LinearMap.ker p'),
      (∀ (s : ↥(LinearMap.ker p)) (i : Fin r), ((g s : ↥(LinearMap.ker p')) : Fin r → B') i = algebraMap B B' ((s : Fin r → B) i)) ∧
      IsBaseChange B' g ∧
      Submodule.span B' (Set.range g) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_isBaseChange_ker_span_range_eq_top_of_flat.solution
