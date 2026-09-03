import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_degree_mapDomain_filter_add_degree_mapDomain_filter_eq_degree_of_deg_eq_one

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.degree_mapDomain_filter_add_degree_mapDomain_filter_eq_degree_of_deg_eq_one
    {K F K' F' : Type*} [Field K] [Field F] [Algebra K F] [Field K'] [Field F'] [Algebra K' F']
    (hdeg : ∀ v : Place K F, v.deg = 1) (hdeg' : ∀ w : Place K' F', w.deg = 1)
    (r₁ r₂ : Place K F → Place K' F') (p₁ p₂ : Place K F → Prop) [DecidablePred p₁] [DecidablePred p₂]
    (hdisj : ∀ V, p₁ V → ¬ p₂ V)
    (E : Divisor K F) (hE : ∀ V ∈ E.support, p₁ V ∨ p₂ V) :
    Divisor.degree (Finsupp.mapDomain r₁ (E.filter p₁)) + Divisor.degree (Finsupp.mapDomain r₂ (E.filter p₂)) = E.degree := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_degree_mapDomain_filter_add_degree_mapDomain_filter_eq_degree_of_deg_eq_one.solution
