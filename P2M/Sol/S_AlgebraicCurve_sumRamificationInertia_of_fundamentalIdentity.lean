import Definitions.Def_AlgebraicCurve_DivisorPushPull
import P2M.Util
namespace P2MW.S_AlgebraicCurve_sumRamificationInertia_of_fundamentalIdentity

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']
    [FundamentalIdentity K F F']
    (hdeg : ∀ v : Place K F, v.deg ≠ 0) : SumRamificationInertia K F F' := by
  refine ⟨fun v => ?_⟩
  have key := FundamentalIdentity.sum_ramificationIndex_mul_deg (K := K) (F := F) (F' := F') v
  have hsum : ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
      = (v.deg : ℤ) * ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [← Place.deg_restrict_mul_inertiaDeg (F := F) w, Place.mem_fiber.mp hw]
    push_cast
    ring
  have hv : (v.deg : ℤ) ≠ 0 := by exact_mod_cast hdeg v
  apply mul_left_cancel₀ hv
  rw [← hsum, key, mul_comm]

#print axioms solution
#check @solution
