import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_InfinitePlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_transport

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceTransport
theorem NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_transport (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ Φ : (NumberField.SIdele.obj E K S) →+ Additive (AdeleRing (𝓞 K) K)ˣ,
      Function.Injective Φ ∧
      Φ.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).toAddSubgroup ∧
      (∀ (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S) (w w' : HeightOneSpectrum (𝓞 K)) (h : g • w = w'),
        ((Additive.toMul (Φ ((NumberField.SIdele.obj E K S).ρ g x)) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w' =
          NumberField.PlaceTransport.transport g h (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w)) ∧
      (∀ (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S) (w w' : InfinitePlace K) (h : g • w = w'),
        ((Additive.toMul (Φ ((NumberField.SIdele.obj E K S).ρ g x)) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w' =
          NumberField.InfinitePlaceTransport.transport g h (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w)) ∧
      (∀ x : NumberField.SUnits.sUnitsRep E K S, Φ ((NumberField.SIdele.diag E K S).hom x) =
        Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
          (NumberField.SUnits.val E K S x))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_transport.solution
