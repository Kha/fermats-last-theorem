import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_span_pair_union_ker_smul_eq_top_of_dualPairing_of_torsion_le_two

set_option autoImplicit false

theorem Module.exists_span_pair_union_ker_smul_eq_top_of_dualPairing_of_torsion_le_two
    {𝒪 : Type*} [CommRing 𝒪] {A : Type*} [CommRing A] [Algebra 𝒪 A]
    {k : Type*} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (π : A →ₐ[𝒪] k)
    {P : Type*} [AddCommGroup P] [Module A P]
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W] [Module A W]
    (hπW : ∀ (r : 𝒪) (w : W), algebraMap 𝒪 A r • w = algebraMap 𝒪 k r • w)
    (β : P →+ Module.Dual k W)
    (hβA : ∀ (a : A) (m : P) (w : W), β (a • m) w = β m (a • w))
    (hβl : ∀ m : P, β m = 0 →
      m ∈ Submodule.span A {x : P | ∃ a : A, π a = 0 ∧ ∃ n : P, x = a • n})
    (hβr : ∀ w : W, (∀ m : P, β m w = 0) → w = 0)
    (h2 : ∃ u v : W, ∀ w : W, (∀ a : A, π a = 0 → a • w = 0) → ∃ c d : k, w = c • u + d • v) :
    ∃ x y : P, Submodule.span A
      ({x, y} ∪ {w : P | ∃ a : A, π a = 0 ∧ ∃ m : P, w = a • m}) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_span_pair_union_ker_smul_eq_top_of_dualPairing_of_torsion_le_two.solution
