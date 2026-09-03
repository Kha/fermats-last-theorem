import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_existsUnique_hom_apply_eq_adicEval_of_natural_of_dense_of_isNilpotent

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.existsUnique_hom_apply_eq_adicEval_of_natural_of_dense_of_isNilpotent
    {p : ℕ} [Fact p.Prime] {L : Type u} [CommRing L] (hp : IsNilpotent (p : L))
    (X X' : CerednikDrinfeld.FormalODModule p L)
    (D : Set (CerednikDrinfeld.Zp2 p × CerednikDrinfeld.Zp2 p))
    (hD : ∀ (k : ℕ) (α β : CerednikDrinfeld.Zp2 p), ∃ d ∈ D,
      d.1 - α ∈ Ideal.span {((p : CerednikDrinfeld.Zp2 p)) ^ k} ∧
        d.2 - β ∈ Ideal.span {((p : CerednikDrinfeld.Zp2 p)) ^ k})
    (t : ∀ (C : Type u) [CommRing C] [Algebra L C], Ideal C → (Fin 2 → C) → (Fin 2 → C))
    (ht_mem : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin 2 → C, (∀ j, x j ∈ J) → ∀ i, t C J x i ∈ J)
    (ht_nat : ∀ (C C' : Type u) [CommRing C] [Algebra L C] [CommRing C'] [Algebra L C']
      (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
      ∀ φ : C →ₐ[L] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : Fin 2 → C, (∀ j, x j ∈ J) → t C' J' (φ ∘ x) = φ ∘ t C J x)
    (ht_add : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ x y : Fin 2 → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) →
        t C J (fun i => MvFormalGroup.adicEval J (Sum.elim x y) (X.F.toPowerSeries i)) =
          fun i => MvFormalGroup.adicEval J (Sum.elim (t C J x) (t C J y)) (X'.F.toPowerSeries i))
    (ht_D : ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
      ∀ d ∈ D, ∀ x : Fin 2 → C, (∀ j, x j ∈ J) →
        t C J (fun i => MvFormalGroup.adicEval J x
            (CerednikDrinfeld.SpecialFormal.Series.addVia X.F (X.act d.1) ((X.act d.2).comp X.varpi) i)) =
          fun i => MvFormalGroup.adicEval J (t C J x)
            (CerednikDrinfeld.SpecialFormal.Series.addVia X'.F (X'.act d.1) ((X'.act d.2).comp X'.varpi) i)) :
    ∃! u : X.Hom X',
      ∀ (C : Type u) [CommRing C] [Algebra L C] (J : Ideal C), IsNilpotent J →
        ∀ x : Fin 2 → C, (∀ j, x j ∈ J) →
          ∀ i, t C J x i = MvFormalGroup.adicEval J x (u.toSeries i) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_existsUnique_hom_apply_eq_adicEval_of_natural_of_dense_of_isNilpotent.solution
