import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_SArchIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_InfinitePlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_SArchIdele_existsUnique_hom_res_obj_comp_toSIdele_eq

set_option autoImplicit false
open IsDedekindDomain NumberField M4aHerbrand
open scoped NumberField.PlaceTransport

theorem NumberField.SArchIdele.existsUnique_hom_res_obj_comp_toSIdele_eq
    (E K K' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra E K] [Algebra E K'] [Algebra K K'] [IsScalarTower E K K'] [IsGalois E K] [IsGalois E K']
    (S : Finset (HeightOneSpectrum (𝓞 E)))

    (Φ : NumberField.SIdele.obj E K S →+ Additive (AdeleRing (𝓞 K) K)ˣ)
    (hΦinj : Function.Injective Φ)
    (hΦrange : Φ.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).toAddSubgroup)
    (hΦS : ∀ (x : NumberField.SIdele.obj E K S) (v : {v // v ∈ S}) (w : HeightOneSpectrum (𝓞 K)) (y : K ≃ₐ[E] K)
      (hy : y • w = NumberField.PlaceAbove.above E K v.1),
      NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) =
        ((Additive.toMul ((x (Sum.inl (Sum.inl v))).1 y) :
          ((NumberField.PlaceAbove.above E K v.1).adicCompletion K)ˣ) : (NumberField.PlaceAbove.above E K v.1).adicCompletion K))
    (hΦout : ∀ (x : NumberField.SIdele.obj E K S) (v : {v // v ∉ S}) (w : HeightOneSpectrum (𝓞 K)) (y : K ≃ₐ[E] K)
      (hy : y • w = NumberField.PlaceAbove.above E K v.1),
      NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) =
        (((Additive.toMul ((x (Sum.inl (Sum.inr v))).1 y) :
          ((NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K)ˣ) :
            (NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K) : (NumberField.PlaceAbove.above E K v.1).adicCompletion K))
    (hΦinf : ∀ (x : NumberField.SIdele.obj E K S) (v : InfinitePlace E) (w : InfinitePlace K) (y : K ≃ₐ[E] K)
      (hy : y • w = NumberField.ArchIdele.above E K v),
      NumberField.InfinitePlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w) =
        ((Additive.toMul ((x (Sum.inr v)).1 y) : ((NumberField.ArchIdele.above E K v).Completion)ˣ) :
          (NumberField.ArchIdele.above E K v).Completion))
    (D : IdeleGaloisDescent (𝓞 K) E K)
    (hΦeq : ∀ (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S),
      Φ ((NumberField.SIdele.obj E K S).ρ g x) = Additive.ofMul (D.unitsAct g (Additive.toMul (Φ x))))

    (Φ' : NumberField.SIdele.obj E K' S →+ Additive (AdeleRing (𝓞 K') K')ˣ)
    (hΦinj' : Function.Injective Φ')
    (hΦrange' : Φ'.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K') K' {w | w.under (𝓞 E) ∈ S}).toAddSubgroup)
    (hΦS' : ∀ (x : NumberField.SIdele.obj E K' S) (v : {v // v ∈ S}) (w : HeightOneSpectrum (𝓞 K')) (y : K' ≃ₐ[E] K')
      (hy : y • w = NumberField.PlaceAbove.above E K' v.1),
      NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ' x) : (AdeleRing (𝓞 K') K')ˣ) : AdeleRing (𝓞 K') K').2 w) =
        ((Additive.toMul ((x (Sum.inl (Sum.inl v))).1 y) :
          ((NumberField.PlaceAbove.above E K' v.1).adicCompletion K')ˣ) : (NumberField.PlaceAbove.above E K' v.1).adicCompletion K'))
    (hΦout' : ∀ (x : NumberField.SIdele.obj E K' S) (v : {v // v ∉ S}) (w : HeightOneSpectrum (𝓞 K')) (y : K' ≃ₐ[E] K')
      (hy : y • w = NumberField.PlaceAbove.above E K' v.1),
      NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ' x) : (AdeleRing (𝓞 K') K')ˣ) : AdeleRing (𝓞 K') K').2 w) =
        (((Additive.toMul ((x (Sum.inl (Sum.inr v))).1 y) :
          ((NumberField.PlaceAbove.above E K' v.1).adicCompletionIntegers K')ˣ) :
            (NumberField.PlaceAbove.above E K' v.1).adicCompletionIntegers K') : (NumberField.PlaceAbove.above E K' v.1).adicCompletion K'))
    (hΦinf' : ∀ (x : NumberField.SIdele.obj E K' S) (v : InfinitePlace E) (w : InfinitePlace K') (y : K' ≃ₐ[E] K')
      (hy : y • w = NumberField.ArchIdele.above E K' v),
      NumberField.InfinitePlaceTransport.transport y hy (((Additive.toMul (Φ' x) : (AdeleRing (𝓞 K') K')ˣ) : AdeleRing (𝓞 K') K').1 w) =
        ((Additive.toMul ((x (Sum.inr v)).1 y) : ((NumberField.ArchIdele.above E K' v).Completion)ˣ) :
          (NumberField.ArchIdele.above E K' v).Completion))
    (D' : IdeleGaloisDescent (𝓞 K') E K')
    (hΦeq' : ∀ (g : K' ≃ₐ[E] K') (x : NumberField.SIdele.obj E K' S),
      Φ' ((NumberField.SIdele.obj E K' S).ρ g x) = Additive.ofMul (D'.unitsAct g (Additive.toMul (Φ' x))))

    (JJ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 K') K')ˣ)
    (hJJ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, (∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S → finPart w z = 1) →
      ∀ w' : HeightOneSpectrum (𝓞 K'), w'.under (𝓞 E) ∉ S → finPart w' (JJ z) = 1)
    (hJJeq : ∀ (g' : K' ≃ₐ[E] K') (z : (AdeleRing (𝓞 K) K)ˣ),
      JJ (D.unitsAct (AlgEquiv.restrictNormalHom K g') z) = D'.unitsAct g' (JJ z)) :
    ∃! jJ : Rep.res (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[E] K') →* (K ≃ₐ[E] K)) (NumberField.SArchIdele.obj E K S) ⟶
        NumberField.SArchIdele.obj E K' S,
      ∀ y : NumberField.SArchIdele.obj E K S,
        Φ' ((NumberField.SArchIdele.toSIdele E K' S).hom (jJ.hom y)) =
          Additive.ofMul (JJ (Additive.toMul (Φ ((NumberField.SArchIdele.toSIdele E K S).hom y)))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_SArchIdele_existsUnique_hom_res_obj_comp_toSIdele_eq.solution
