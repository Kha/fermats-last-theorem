import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import P2M.Util
namespace P2MW.S_AlgebraicCurve_ComponentChart_ord_residue_nonneg_of_not_mem_nodes_of_forall_mem_dom_ord_nonneg

set_option autoImplicit false
set_option Elab.async false

open AlgebraicCurve IsLocalRing

namespace ZXPoleNodes

theorem mapDomain_nonneg {α β : Type*} (g : α → β) (D : α →₀ ℤ) (hD : ∀ a, 0 ≤ D a) (b : β) :
    0 ≤ Finsupp.mapDomain g D b := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finset.sum_nonneg fun a _ => ?_
  show 0 ≤ (Finsupp.single (g a) (D a)) b
  rw [Finsupp.single_apply]
  split_ifs
  · exact hD a
  · exact le_rfl

end ZXPoleNodes

open ZXPoleNodes in

theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (g : F) (hg0 : g ≠ 0) (hg : g ∈ C.integers) (hres : C.residue ⟨g, hg⟩ ≠ 0)
    (hpole : ∀ P ∈ C.dom, 0 ≤ P.ord g)
    (v : Place (ResidueField A) Fbar) (hv : v ∉ C.nodes) :
    0 ≤ v.ord (C.residue ⟨g, hg⟩) := by
  classical
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) g hg0
  have key := C.mapDomain_placeMap ⟨g, hg⟩ hres (D.filter (· ∈ C.dom))
    (fun P hP => by rw [Finsupp.filter_apply_pos _ _ hP, hD])
    (fun P hP => by rw [Finsupp.filter_apply_neg _ _ hP]) v hv
  rw [← key]
  apply mapDomain_nonneg
  intro P
  by_cases hP : P ∈ C.dom
  · rw [Finsupp.filter_apply_pos _ _ hP, hD]; exact hpole P hP
  · rw [Finsupp.filter_apply_neg _ _ hP]
