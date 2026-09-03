import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_det_eq_of_sq_sub_trace_smul_add_smul_one_eq_zero

set_option autoImplicit false

theorem Representation.det_eq_of_sq_sub_trace_smul_add_smul_one_eq_zero
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (hV : Module.finrank k V = 2)
    (ρV : G →* Module.End k V)
    {M : Type} [AddCommGroup M] [Module k M] [Nontrivial M]
    (ρM : G →* Module.End k M) (d : G →* kˣ)
    (hrel : ∀ g : G,
      ρM g * ρM g - (LinearMap.trace k V (ρV g)) • ρM g + ((d g : kˣ) : k) • (1 : Module.End k M) = 0) :
    ∀ g : G, LinearMap.det (ρV g) = d g := by p2m_exact_reverting @_root_.P2MW.S_Representation_det_eq_of_sq_sub_trace_smul_add_smul_one_eq_zero.solution
