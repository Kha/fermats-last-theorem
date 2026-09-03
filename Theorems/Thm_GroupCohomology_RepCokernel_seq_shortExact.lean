import Mathlib
import Definitions.Def_GroupCohomology_RepCokernel
import P2M.Util
import P2M.Sol.S_GroupCohomology_RepCokernel_seq_shortExact

set_option autoImplicit false
universe u
open CategoryTheory
theorem GroupCohomology.RepCokernel.seq_shortExact {k G : Type u} [CommRing k] [Group G] {X Y : Rep.{u} k G} (f : X ⟶ Y)
    (hf : Function.Injective f.hom) : (GroupCohomology.RepCokernel.seq f).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_GroupCohomology_RepCokernel_seq_shortExact.solution
