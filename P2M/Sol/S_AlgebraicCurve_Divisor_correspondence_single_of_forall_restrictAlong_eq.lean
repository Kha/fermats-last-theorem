import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_single
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Divisor_correspondence_single_of_forall_restrictAlong_eq

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (v : Place K F) (hcoll : ∀ w ∈ Place.fiberAlong φ hφ v, w.restrictAlong ψ hψ = v) (n : ℤ) : Divisor.correspondence φ ψ hφ hψ (Finsupp.single v n) = Finsupp.single v (n * ∑ w ∈ Place.fiberAlong φ hφ v, (w.ramificationIndexAlong φ : ℤ) * (w.inertiaDegAlong ψ hψ : ℤ)) := by
  rw [Divisor.correspondence_single φ ψ hφ hψ v n, Finset.mul_sum, Finsupp.single_finsetSum]
  exact Finset.sum_congr rfl fun w hw => by rw [hcoll w hw, mul_assoc]

end
