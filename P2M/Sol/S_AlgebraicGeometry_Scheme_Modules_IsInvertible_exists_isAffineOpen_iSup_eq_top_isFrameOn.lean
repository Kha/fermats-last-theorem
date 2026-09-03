import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_iSup_eq_top_isFrameOn

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FrameCoverT

theorem main {X : Scheme.{u}} [CompactSpace ↥X] (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ (n : ℕ) (W : ULift.{u} (Fin n) → X.Opens), (∀ l, IsAffineOpen (W l)) ∧ (⨆ l, W l) = ⊤ ∧
      ∃ m : ∀ l, Γ(M, W l), ∀ l, Scheme.Modules.IsFrameOn (m l) (W l) := by
  classical

  have hx : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ ∃ s : Γ(M, V), Scheme.Modules.IsFrameOn s V := by
    intro x
    obtain ⟨U, hxU, ⟨eU⟩⟩ := hM.exists_trivialization x
    obtain ⟨s, hs⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit U eU
    obtain ⟨V, hV, hxV, hVU⟩ :=
      (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hxU
    exact ⟨V, hV, hxV, M.presheaf.map (homOfLE hVU).op s, (hs.map (homOfLE hVU)).mono hVU⟩
  choose V hVaff hxV hfr using hx

  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => ((V x : X.Opens) : Set X))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  let e : Fin t.card ≃ ↥t := t.equivFin.symm
  refine ⟨t.card, fun l => V (e l.down).1, fun l => hVaff _, ?_, fun l => (hfr (e l.down).1).choose,
    fun l => (hfr (e l.down).1).choose_spec⟩

  apply le_antisymm le_top
  intro x _
  obtain ⟨y, hy⟩ := Set.mem_iUnion.1 (ht (Set.mem_univ x))
  obtain ⟨hyt, hxy⟩ := Set.mem_iUnion.1 hy
  refine Opens.mem_iSup.2 ⟨ULift.up (e.symm ⟨y, hyt⟩), ?_⟩
  simpa using hxy

end FrameCoverT

theorem solution {X : Scheme.{u}} [CompactSpace ↥X] (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ (n : ℕ) (W : ULift.{u} (Fin n) → X.Opens), (∀ l, IsAffineOpen (W l)) ∧ (⨆ l, W l) = ⊤ ∧
      ∃ m : ∀ l, Γ(M, W l), ∀ l, Scheme.Modules.IsFrameOn (m l) (W l) :=
  FrameCoverT.main M hM

#print axioms solution
