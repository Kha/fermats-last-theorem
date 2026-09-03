import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SUnitsModule
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation IsDedekindDomain NumberField NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

theorem NumberField.LevelArith.exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary
    (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [Normal ↥L ↥(levelField L F hLF)]
    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →*
      (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hιg : ∀ g : ↥L.fixingSubgroup,
      ι (levelGal L F hLF g) = (g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
    (hφval : ∀ x,
      ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) :
          ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hloc : ∀ (q : ↥S) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ∃ c : ↥(L.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes)))) →
          sUnitsMaxRep S L,
        IsLevelConstant₁
            ((((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).comp
              (L.fixingSubgroup.comap
                ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes)))).subtype)) c ∧
          ∀ g h : ↥(L.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes)))),
            ((f (((((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).subgroupComap
                      L.fixingSubgroup g : ↥L.fixingSubgroup) :
                    ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype),
                  ((((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).subgroupComap
                      L.fixingSubgroup h : ↥L.fixingSubgroup) :
                    ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
                (sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
              sUnitsMaxRep S L) =
              (sUnitsMaxRep S L).ρ
                  (((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).subgroupComap
                    L.fixingSubgroup g) (c h) - c (g * h) + c g)
    (v : {v // v ∈ placesOverPrimesFinset ↥L S}) :
    ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : Algebra ↥L K'')
      (_ : Algebra ↥(levelField L F hLF) K'')
      (_ : IsScalarTower ↥L ↥(levelField L F hLF) K'') (_ : IsGalois ↥L K'') (w'' : HeightOneSpectrum (𝓞 K''))
      (_ : HeightOneSpectrum.under (𝓞 ↥(levelField L F hLF)) w'' = PlaceAbove.above ↥L ↥(levelField L F hLF) v.1)
      (y : PlaceDecomp.decomp ↥L K'' w'' →
        Rep.ofMulDistribMulAction (PlaceDecomp.decomp ↥L K'' w'') (w''.adicCompletion K'')ˣ),
      ∀ g h : PlaceDecomp.decomp ↥L K'' w'',
        Additive.ofMul (Units.map (algebraMap K'' (w''.adicCompletion K'')).toMonoidHom
            (Units.map (algebraMap ↥(levelField L F hLF) K'').toMonoidHom
              (SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)
                ((mapCocycles₂ ι φ f)
                  (AlgEquiv.restrictNormalHom ↥(levelField L F hLF) (g : K'' ≃ₐ[↥L] K''),
                    AlgEquiv.restrictNormalHom ↥(levelField L F hLF) (h : K'' ≃ₐ[↥L] K'')))))) =
          (Rep.ofMulDistribMulAction (PlaceDecomp.decomp ↥L K'' w'') (w''.adicCompletion K'')ˣ).ρ g (y h) -
            y (g * h) + y g := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary.solution
