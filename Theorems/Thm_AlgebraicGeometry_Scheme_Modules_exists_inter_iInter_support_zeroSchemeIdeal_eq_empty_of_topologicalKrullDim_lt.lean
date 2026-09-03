import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_inter_iInter_support_zeroSchemeIdeal_eq_empty_of_topologicalKrullDim_lt

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.Modules.exists_inter_iInter_support_zeroSchemeIdeal_eq_empty_of_topologicalKrullDim_lt
    {k : Type u} [Field k] [Infinite k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [NoetherianSpace V]
    {n : ℕ} (N : Fin n → V.Modules) (hN : ∀ i, Scheme.Modules.IsInvertible (N i))
    (hbpf : ∀ (i : Fin n) (x : V), ∃ s : 𝟙_ V.Modules ⟶ N i, x ∉ (Scheme.Modules.zeroSchemeIdeal s).support)
    (B : Set V) (hB : IsClosed B) (hdim : topologicalKrullDim B < n) :
    ∃ s : ∀ i : Fin n, (𝟙_ V.Modules ⟶ N i),
      B ∩ ⋂ i, ((Scheme.Modules.zeroSchemeIdeal (s i)).support : Set V) = ∅ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_inter_iInter_support_zeroSchemeIdeal_eq_empty_of_topologicalKrullDim_lt.solution
