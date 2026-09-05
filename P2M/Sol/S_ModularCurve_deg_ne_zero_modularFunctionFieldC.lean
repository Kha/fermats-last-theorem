module

public import Definitions.Def_ModularCurve_JqCoeff
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.Def_AlgebraicCurve_RatFuncPlaces
public import Definitions.Def_AlgebraicCurve_DivisorPushPull
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_deg_ne_zero
import P2M.Sol.S_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional
import P2M.Sol.S_ModularCurve_transcendental_jqModC
import P2M.Sol.S_ModularCurve_finiteDimensional_adjoin_jqNModC
import P2M.Sol.S_ModularCurve_nonempty_modularPolynomialData
import P2M.Util

namespace P2MW.S_ModularCurve_deg_ne_zero_modularFunctionFieldC

open AlgebraicCurve ModularCurve IntermediateField Polynomial

noncomputable section

namespace S09T3

section Generic
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F']

theorem deg_ne_zero_of_restrict (w : Place K F') (h : (w.restrict F).deg ≠ 0) : w.deg ≠ 0 := by
  rw [← w.deg_restrict_mul_inertiaDeg (F := F)]
  exact mul_ne_zero h (Place.inertiaDeg_pos_of_finiteDimensional (F := F) w).ne'
end Generic

variable (K : Type*) [Field K]

abbrev Fj : IntermediateField K (LaurentSeries K) := adjoin K ({jqModC K} : Set (LaurentSeries K))

noncomputable def psi : RatFunc K →ₐ[K] LaurentSeries K :=
  RatFunc.liftAlgHom (aeval (jqModC K))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (transcendental_iff_injective.mp (transcendental_jqModC K)))

theorem psi_injective : Function.Injective (psi K) :=
  RatFunc.liftAlgHom_injective _ (transcendental_iff_injective.mp (transcendental_jqModC K))

theorem psi_mem (f : RatFunc K) : psi K f ∈ Fj K := by
  rw [← f.num_div_denom, psi, RatFunc.liftAlgHom_apply_div]
  exact (mem_adjoin_simple_iff K _).mpr ⟨_, _, rfl⟩

noncomputable def ratFuncEquiv : RatFunc K ≃+* Fj K :=
  RingEquiv.ofBijective
    ({ toFun := fun f => ⟨psi K f, psi_mem K f⟩
       map_one' := Subtype.ext (map_one (psi K))
       map_mul' := fun a b => Subtype.ext (map_mul (psi K) a b)
       map_zero' := Subtype.ext (map_zero (psi K))
       map_add' := fun a b => Subtype.ext (map_add (psi K) a b) } : RatFunc K →+* Fj K)
    ⟨fun a b hab => psi_injective K (congrArg Subtype.val hab), by
      rintro ⟨x, hx⟩
      obtain ⟨r, s, rfl⟩ := (mem_adjoin_simple_iff K _).mp hx
      refine ⟨algebraMap _ _ r / algebraMap _ _ s, Subtype.ext ?_⟩
      show psi K (algebraMap _ _ r / algebraMap _ _ s) = _
      rw [psi, RatFunc.liftAlgHom_apply_div]⟩

theorem ratFuncEquiv_algebraMap (a : K) :
    ratFuncEquiv K (algebraMap K (RatFunc K) a) = algebraMap K (Fj K) a :=
  Subtype.ext (by exact (psi K).commutes a)

theorem deg_ne_zero_Fj (v : Place K (Fj K)) : v.deg ≠ 0 := by
  rw [← Place.deg_congrRingEquiv (ratFuncEquiv K).symm
    (Place.symm_algebraMap_comm _ (ratFuncEquiv_algebraMap K)) v]
  exact RationalFunctionField.deg_ne_zero _

variable (N : ℕ) [NeZero N]

abbrev FjN : IntermediateField (Fj K) (LaurentSeries K) :=
  adjoin (Fj K) ({jqNModC K N} : Set (LaurentSeries K))

theorem modularFunctionFieldC_eq_restrictScalars :
    modularFunctionFieldC K N = (FjN K N).restrictScalars K := by
  show modularFunctionFieldC K N =
    (adjoin (adjoin K ({jqModC K} : Set (LaurentSeries K))) ({jqNModC K N} : Set (LaurentSeries K))).restrictScalars K
  erw [adjoin_adjoin_left]
  rw [Set.singleton_union]
  rfl

noncomputable def toFjN : modularFunctionFieldC K N ≃+* FjN K N :=
  (equivOfEq (modularFunctionFieldC_eq_restrictScalars K N)).toRingEquiv.trans
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }

theorem toFjN_algebraMap (a : K) :
    toFjN K N (algebraMap K (modularFunctionFieldC K N) a) = algebraMap K (FjN K N) a :=
  Subtype.ext rfl

end S09T3

end

open S09T3 in
theorem solution (K : Type*) [Field K] (N : ℕ) [NeZero N] (w : Place K (modularFunctionFieldC K N)) : w.deg ≠ 0 := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  haveI : FiniteDimensional (Fj K) (FjN K N) := finiteDimensional_adjoin_jqNModC K data
  rw [← Place.deg_congrRingEquiv (toFjN K N) (toFjN_algebraMap K N) w]
  exact deg_ne_zero_of_restrict (F := Fj K) _ (deg_ne_zero_Fj K _)
end S_ModularCurve_deg_ne_zero_modularFunctionFieldC
end P2MW

public section
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

open AlgebraicCurve ModularCurve

theorem ModularCurve.deg_ne_zero_modularFunctionFieldC (K : Type*) [Field K] (N : ℕ) [NeZero N] (w : Place K (modularFunctionFieldC K N)) : w.deg ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_deg_ne_zero_modularFunctionFieldC.solution
end
