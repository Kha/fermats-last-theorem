import Mathlib
import P2M.Util
import P2M.Sol.S_Rep_nonempty_groupCohomology_res_iso_res_range

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.nonempty_groupCohomology_res_iso_res_range {k G P : Type u} [CommRing k] [Group G] [Group P]
    (f : P →* G) (hf : Function.Injective f) (A : Rep.{u} k G) (n : ℕ) :
    Nonempty (groupCohomology (Rep.res f A) n ≅ groupCohomology (Rep.res f.range.subtype A) n) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_groupCohomology_res_iso_res_range.solution
