import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_exists_coind_res_linearEquiv_quotient_fun

set_option autoImplicit false

universe u

open CategoryTheory
theorem Rep.exists_coind_res_linearEquiv_quotient_fun {k S : Type u} [CommRing k] [Group S] (S'' : Subgroup S) [S''.Normal] (N : Rep.{u} k S) :
    ∃ e : Rep.coind S''.subtype (Rep.res S''.subtype N) ≃ₗ[k] (S ⧸ S'' → N),
      ∀ (s : S) (f : Rep.coind S''.subtype (Rep.res S''.subtype N)) (q : S ⧸ S''),
        e ((Rep.coind S''.subtype (Rep.res S''.subtype N)).ρ s f) q = N.ρ s (e f (q * (s : S ⧸ S''))) := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_coind_res_linearEquiv_quotient_fun.solution
