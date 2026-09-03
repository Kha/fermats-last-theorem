import Mathlib
import Definitions.Def_GroupCohomology_RepCokernel
import P2M.Util
namespace P2MW.S_GroupCohomology_RepCokernel_seq_shortExact

set_option autoImplicit false
universe u
open CategoryTheory

theorem solution {k G : Type u} [CommRing k] [Group G] {X Y : Rep.{u} k G} (f : X ⟶ Y)
    (hf : Function.Injective f.hom) : (GroupCohomology.RepCokernel.seq f).ShortExact where
  exact := (forget₂ (Rep.{u} k G) (ModuleCat k)).reflects_exact_of_faithful _ <|
      (ShortComplex.moduleCat_exact_iff _).2 fun x hx => by
        obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 hx
        exact ⟨a, ha⟩
  mono_f := (Rep.mono_iff_injective _).2 hf
  epi_g := (Rep.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
