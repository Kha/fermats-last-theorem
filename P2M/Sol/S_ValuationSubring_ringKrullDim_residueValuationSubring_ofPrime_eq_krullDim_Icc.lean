import Mathlib
import Definitions.Def_ValuationSubring_ResidueValuationSubring
import P2M.Util
namespace P2MW.S_ValuationSubring_ringKrullDim_residueValuationSubring_ofPrime_eq_krullDim_Icc

open IsLocalRing

namespace CompVIccSol

variable {L : Type*} [Field L] (A S : ValuationSubring L) (h : A ≤ S)

def subtypeIso {α β : Type*} [LE α] [LE β] (f : α ≃o β) {p : α → Prop} {q : β → Prop}
    (hpq : ∀ a, p a ↔ q (f a)) : {a // p a} ≃o {b // q b} where
  toEquiv := f.toEquiv.subtypeEquiv hpq
  map_rel_iff' {a b} := by
    change f a ≤ f b ↔ (a : α) ≤ b
    exact f.map_rel_iff

abbrev Ω (A : ValuationSubring L) := {T : ValuationSubring L // A ≤ T}

def σ : Ω A := ⟨S, h⟩

noncomputable def isoIic :
    {P : (PrimeSpectrum A)ᵒᵈ // OrderDual.ofDual P ∈
        PrimeSpectrum.zeroLocus ((A.idealOfLE S h : Ideal A) : Set A)} ≃o Set.Iic (σ A S h) :=
  subtypeIso (ValuationSubring.primeSpectrumOrderEquiv A) fun P => by
    change (A.idealOfLE S h : Set A) ⊆ (OrderDual.ofDual P).asIdeal ↔
      (⟨A.ofPrime (OrderDual.ofDual P).asIdeal, _⟩ : Ω A) ≤ ⟨S, h⟩
    rw [SetLike.coe_subset_coe]
    constructor
    · intro hle
      change A.ofPrime (OrderDual.ofDual P).asIdeal ≤ S
      conv_rhs => rw [← ValuationSubring.ofPrime_idealOfLE A S h]
      exact ValuationSubring.ofPrime_le_of_le A _ _ hle
    · intro hle
      change A.ofPrime (OrderDual.ofDual P).asIdeal ≤ S at hle
      have := ValuationSubring.idealOfLE_le_of_le A _ _ (A.le_ofPrime _) h hle
      rwa [ValuationSubring.idealOfLE_ofPrime] at this

theorem krullDim_zeroLocus_eq :
    Order.krullDim (PrimeSpectrum.zeroLocus ((A.idealOfLE S h : Ideal A) : Set A)) =
      Order.krullDim (Set.Iic (σ A S h)) := by
  rw [← Order.krullDim_eq_of_orderIso (isoIic A S h), ← Order.krullDim_orderDual]
  exact Order.krullDim_eq_of_orderIso
    { toEquiv := Equiv.refl _
      map_rel_iff' := Iff.rfl }

theorem ringKrullDim_residueValuationSubring :
    ringKrullDim (A.residueValuationSubring S h) =
      Order.krullDim (PrimeSpectrum.zeroLocus ((A.idealOfLE S h : Ideal A) : Set A)) :=
  Order.krullDim_eq_of_orderIso
    (Ideal.primeSpectrumOrderIsoZeroLocusOfSurj (A.toResidueValuationSubring S h)
      (A.toResidueValuationSubring_surjective S h) (A.ker_toResidueValuationSubring S h))

theorem ringKrullDim_ofPrime_pair (Q P : Ideal A) [Q.IsPrime] [P.IsPrime] (hQP : Q ≤ P) :
    ringKrullDim ((A.ofPrime P).residueValuationSubring (A.ofPrime Q)
        (ValuationSubring.ofPrime_le_of_le A Q P hQP)) =
      Order.krullDim (Set.Icc (⟨Q, inferInstance⟩ : PrimeSpectrum A) ⟨P, inferInstance⟩) := by
  have h' : A.ofPrime P ≤ A.ofPrime Q := ValuationSubring.ofPrime_le_of_le A Q P hQP
  rw [ringKrullDim_residueValuationSubring (A.ofPrime P) (A.ofPrime Q) h',
    krullDim_zeroLocus_eq (A.ofPrime P) (A.ofPrime Q) h']

  let e₁ : Set.Iic (σ (A.ofPrime P) (A.ofPrime Q) h') ≃o
      {T : Ω A // A.ofPrime P ≤ T.1 ∧ T.1 ≤ A.ofPrime Q} :=
    { toFun := fun T => ⟨⟨T.1.1, (A.le_ofPrime P).trans T.1.2⟩, T.1.2, T.2⟩
      invFun := fun T => ⟨⟨T.1.1, T.2.1⟩, T.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  let e₂ : {q : (PrimeSpectrum A)ᵒᵈ // OrderDual.ofDual q ∈
      Set.Icc (⟨Q, inferInstance⟩ : PrimeSpectrum A) ⟨P, inferInstance⟩} ≃o
      {T : Ω A // A.ofPrime P ≤ T.1 ∧ T.1 ≤ A.ofPrime Q} :=
    subtypeIso (ValuationSubring.primeSpectrumOrderEquiv A) fun q => by
      change Q ≤ (OrderDual.ofDual q).asIdeal ∧ (OrderDual.ofDual q).asIdeal ≤ P ↔
        A.ofPrime P ≤ A.ofPrime (OrderDual.ofDual q).asIdeal ∧
          A.ofPrime (OrderDual.ofDual q).asIdeal ≤ A.ofPrime Q
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨ValuationSubring.ofPrime_le_of_le A _ _ h2,
          ValuationSubring.ofPrime_le_of_le A _ _ h1⟩
      · rintro ⟨h1, h2⟩
        constructor
        · have := ValuationSubring.idealOfLE_le_of_le A _ _ (A.le_ofPrime _) (A.le_ofPrime _) h2
          rwa [ValuationSubring.idealOfLE_ofPrime, ValuationSubring.idealOfLE_ofPrime] at this
        · have := ValuationSubring.idealOfLE_le_of_le A _ _ (A.le_ofPrime _) (A.le_ofPrime _) h1
          rwa [ValuationSubring.idealOfLE_ofPrime, ValuationSubring.idealOfLE_ofPrime] at this
  rw [Order.krullDim_eq_of_orderIso e₁, ← Order.krullDim_eq_of_orderIso e₂,
    ← Order.krullDim_orderDual (α := Set.Icc _ _)]
  exact Order.krullDim_eq_of_orderIso
    { toEquiv := Equiv.refl _
      map_rel_iff' := Iff.rfl }

end CompVIccSol

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L) (Q P : Ideal A) [Q.IsPrime] [P.IsPrime]
    (hQP : Q ≤ P) :
    ringKrullDim ((A.ofPrime P).residueValuationSubring (A.ofPrime Q)
        (ValuationSubring.ofPrime_le_of_le A Q P hQP)) =
      Order.krullDim (Set.Icc (⟨Q, inferInstance⟩ : PrimeSpectrum A) ⟨P, inferInstance⟩) :=
  CompVIccSol.ringKrullDim_ofPrime_pair A Q P hQP
