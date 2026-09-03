import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Annulus_ord_sub_div_sub_and_residue_src_eq_one_and_residue_tgt_eq_of_depth_eq

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Annulus.ord_sub_div_sub_and_residue_src_eq_one_and_residue_tgt_eq_of_depth_eq
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, HasPrincipalDivisors (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (e₀ : Fin m) (P P' : Place L F) (hP : P ∈ (An e₀).dom) (hP' : P' ∈ (An e₀).dom) (hPP' : P ≠ P')
    (d : ℕ) (u u' : Aˣ) (h : P.evalAt (An e₀).param ∈ A) (h' : P'.evalAt (An e₀).param ∈ A)
    (hd : (⟨P.evalAt (An e₀).param, h⟩ : A) = u * π ^ d)
    (hd' : (⟨P'.evalAt (An e₀).param, h'⟩ : A) = u' * π ^ d)
    :
    let g : F := ((An e₀).param - algebraMap L F (P.evalAt (An e₀).param)) /
      ((An e₀).param - algebraMap L F (P'.evalAt (An e₀).param))
    g ≠ 0 ∧
      (∀ Q : Place L F, Q.ord g = Q.ord ((An e₀).param - algebraMap L F (P.evalAt (An e₀).param)) -
        Q.ord ((An e₀).param - algebraMap L F (P'.evalAt (An e₀).param))) ∧
      (∀ Q ∈ (An e₀).dom, Q.ord g = (Finsupp.single P 1 - Finsupp.single P' 1 : Divisor L F) Q) ∧
      (∃ hs : g ∈ (C (src e₀)).integers, (C (src e₀)).residue ⟨g, hs⟩ = 1) ∧
      (∃ ht : g ∈ (C (tgt e₀)).integers, (C (tgt e₀)).residue ⟨g, ht⟩ =
        algebraMap (IsLocalRing.ResidueField A) (Fbar (tgt e₀)) (IsLocalRing.residue A ((u : A) * ↑u'⁻¹))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Annulus_ord_sub_div_sub_and_residue_src_eq_one_and_residue_tgt_eq_of_depth_eq.solution
