import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Definitions.Def_AlgebraicCurve_AffinoidCentre
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ComponentChart_eq_integers_or_existsUnique_isCentre_of_forall_tubeBounded_mem_of_regular

set_option autoImplicit false

namespace AlgebraicCurve

open IsLocalRing
open scoped Pointwise

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem ComponentChart.eq_integers_or_existsUnique_isCentre_of_forall_tubeBounded_mem_of_regular
    (C : ComponentChart A F Fbar) (N : Finset (Place (ResidueField A) Fbar))
    (hC : C.HasAffinoidLifting N) (hdict : ComponentChart.HasPlaceDictionary (A := A) N)
    (hreg : ∀ (f : F) (hf : f ∈ C.integers), C.tubeBounded f →
      ∀ Q : Place (ResidueField A) Fbar, Q ∉ N → C.residue ⟨f, hf⟩ ∈ Q.toValuationSubring)
    (hdim : ∀ 𝔭 : Ideal (ComponentChart.regOff (A := A) N), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭.IsMaximal)
    (hN : N.Nonempty) (hrat : ∀ P ∈ C.dom, P.IsRational)
    (O : ValuationSubring F) (hO : ∀ x : L, algebraMap L F x ∈ O ↔ x ∈ A)
    (hRO : ∀ f : F, C.tubeBounded f → f ∈ O) :
    O = C.integers ∨ ∃! Q : Place (ResidueField A) Fbar, C.IsCentre N O Q := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ComponentChart_eq_integers_or_existsUnique_isCentre_of_forall_tubeBounded_mem_of_regular.solution
