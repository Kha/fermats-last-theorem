import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemistableModel_isOpen_compl_closures_and_mem_iff

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve IsLocalRing

universe u v w u₁ u₂

theorem AlgebraicCurve.SemistableModel.isOpen_compl_closures_and_mem_iff
    {L : Type u} [Field L] {A : ValuationSubring L} {F : Type v} [Field F] [Algebra L F]
    {ιV : Type u₁} {ιE : Type u₂} [Fintype ιV] [Fintype ιE]
    {Fbar : ιV → Type w} [∀ i, Field (Fbar i)] [∀ i, Algebra (ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (ResidueField A) (Fbar (src e))} {xt : ∀ e, Place (ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (hchart : ∀ (P : Place L F) (i : ιV), P ∈ (C i).dom → (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) :
    let U₀ : Finset (Place L F) → Set M.X := fun S => (⋃ P ∈ S, {x : M.X | M.pt P ⤳ x})ᶜ
    let U₁ : ιV → Finset (Place L F) → Set M.X := fun i B =>
      ((⋃ j ∈ {j : ιV | j ≠ i}, {x : M.X | M.gen j ⤳ x}) ∪ Set.range M.nd ∪ ⋃ P ∈ B, {x : M.X | M.pt P ⤳ x})ᶜ
    (∀ S, IsOpen (U₀ S)) ∧ (∀ i B, IsOpen (U₁ i B)) ∧
    (∀ S, genericPoint M.X ∈ U₀ S) ∧ (∀ i B, genericPoint M.X ∈ U₁ i B) ∧
    (∀ S (P : Place L F), M.pt P ∈ U₀ S ↔ P ∉ S) ∧
    (∀ i B (P : Place L F), M.pt P ∈ U₁ i B ↔ P ∉ B) ∧
    (∀ S (j : ιV), M.gen j ∈ U₀ S) ∧ (∀ i B (j : ιV), M.gen j ∈ U₁ i B ↔ j = i) ∧
    (∀ S (e : ιE), M.nd e ∈ U₀ S ↔ ∀ P ∈ S, P ∉ (An e).dom) ∧ (∀ i B (e : ιE), M.nd e ∉ U₁ i B) ∧
    (∀ S (j : ιV) (Q' : {Q : Place (ResidueField A) (Fbar j) // Q ∉ (C j).nodes}),
      M.sm j Q' ∈ U₀ S ↔ ∀ P ∈ S, ∀ hP : P ∈ (C j).dom, (C j).placeMap P ≠ Q'.1) ∧
    (∀ i B (j : ιV) (Q' : {Q : Place (ResidueField A) (Fbar j) // Q ∉ (C j).nodes}),
      M.sm j Q' ∈ U₁ i B ↔ j = i ∧ ∀ P ∈ B, ∀ hP : P ∈ (C j).dom, (C j).placeMap P ≠ Q'.1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemistableModel_isOpen_compl_closures_and_mem_iff.solution
