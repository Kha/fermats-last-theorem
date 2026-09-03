import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_AlgFunctor_exists_pt_eq_of_forall_isLocalization_atPrime

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.AlgFunctor.exists_pt_eq_of_forall_isLocalization_atPrime
    {C : Type} [CommRing C] (P : AlgFunctor C)

    (hsep : ∀ (A : Type) [CommRing A] [Algebra C A] (n : ℕ) (f : Fin n → A), Ideal.span (Set.range f) = ⊤ →
      ∀ (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra C (B i)]
        [∀ i, IsScalarTower C A (B i)] [∀ i, IsLocalization.Away (f i) (B i)] (a b : P.obj A),
      (∀ i, P.map (IsScalarTower.toAlgHom C A (B i)) a = P.map (IsScalarTower.toAlgHom C A (B i)) b) → a = b)

    (S : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S]

    (hlfp : ∀ (g : S) (A : Type) [CommRing A] [Algebra S A] [Algebra C A] [IsScalarTower C S A] [IsLocalization.Away g A]
      [IsNoetherianRing A] (𝔭 : Ideal A) [𝔭.IsPrime]
      (L : Type) [CommRing L] [Algebra A L] [Algebra C L] [IsScalarTower C A L] [IsLocalization.AtPrime L 𝔭] (a b : P.obj A),
      P.map (IsScalarTower.toAlgHom C A L) a = P.map (IsScalarTower.toAlgHom C A L) b →
      ∃ (f : A) (_ : f ∉ 𝔭) (Af : Type) (_ : CommRing Af) (_ : Algebra A Af) (_ : Algebra C Af) (_ : IsScalarTower C A Af)
        (_ : IsLocalization.Away f Af),
        P.map (IsScalarTower.toAlgHom C A Af) a = P.map (IsScalarTower.toAlgHom C A Af) b)

    {W : Scheme.{0}} (fW : W ⟶ Spec (CommRingCat.of C)) (hW : LocallyOfFiniteType fW)
    (pt : ∀ (T : Type) [CommRing T] [Algebra C T], (Scheme.nilpPoints fW).obj T → P.obj T)
    (hnat : ∀ (T T' : Type) [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T'] (φ : T →ₐ[C] T')
      (w : (Scheme.nilpPoints fW).obj T), pt T' ((Scheme.nilpPoints fW).map φ w) = P.map φ (pt T w))
    (hinj : ∀ (T : Type) [CommRing T] [Algebra C T] [IsNoetherianRing T]
      (w w' : (Scheme.nilpPoints fW).obj T), pt T w = pt T w' → w = w')

    (x : P.obj S)
    (hloc : ∀ (𝔭 : Ideal S) [𝔭.IsPrime] (L : Type) [CommRing L] [Algebra S L] [Algebra C L] [IsScalarTower C S L]
      [IsLocalization.AtPrime L 𝔭],
      ∃ w : (Scheme.nilpPoints fW).obj L, pt L w = P.map (IsScalarTower.toAlgHom C S L) x) :
    ∃ w : (Scheme.nilpPoints fW).obj S, pt S w = x := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_AlgFunctor_exists_pt_eq_of_forall_isLocalization_atPrime.solution
