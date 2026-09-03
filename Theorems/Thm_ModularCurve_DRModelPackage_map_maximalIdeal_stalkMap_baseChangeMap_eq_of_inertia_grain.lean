import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_ModularCurve_ProlongationTuple
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackage_map_maximalIdeal_stalkMap_baseChangeMap_eq_of_inertia_grain

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve
open IsLocalRing

theorem ModularCurve.DRModelPackage.map_maximalIdeal_stalkMap_baseChangeMap_eq_of_inertia_grain
    (p : ℕ) [Fact p.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime p)
    (𝔛 : DRModelPackage p)
    {k : Type} [Field k] [CharP k p] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* k)
    (htoκ : ∀ o : O, toκ o = red ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)
      ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) :
        ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)
    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))

    (hrat : Function.Surjective ((IsLocalRing.residue ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((DRModel.baseChangeMap toκ).base ((𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))))).comp (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ ((DRModel.baseChangeMap toκ).base ((𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))) trivial).hom.comp (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)))) :
    Ideal.map ((DRModel.baseChangeMap toκ).stalkMap ((𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))).hom
        (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
    Ideal.map ((DRModel.baseChangeMap toκ).stalkMap ((𝔛.compZero k).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))).hom
        (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackage_map_maximalIdeal_stalkMap_baseChangeMap_eq_of_inertia_grain.solution
