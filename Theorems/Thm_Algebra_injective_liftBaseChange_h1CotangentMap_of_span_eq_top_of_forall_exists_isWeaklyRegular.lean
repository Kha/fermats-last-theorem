import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular

set_option autoImplicit false

universe u v w w'

open scoped TensorProduct

theorem Algebra.injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {T : Type w} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat S T]
    (s : Set T) (hs : Ideal.span s = ⊤)
    (H : ∀ g ∈ s, ∃ (ι : Type w') (x : ι → Localization.Away g) (f : List (MvPolynomial ι S)),
      Function.Surjective (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] Localization.Away g) ∧
      RingHom.ker (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] Localization.Away g) =
        Ideal.ofList f ∧
      ∀ (m : Ideal (MvPolynomial ι S)) [m.IsMaximal], Ideal.ofList f ≤ m →
        RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime m)
          (f.map (algebraMap (MvPolynomial ι S) (Localization.AtPrime m)))) :
    Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.solution
