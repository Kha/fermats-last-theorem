import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_finite_fppfCohomology_of_shortExact

set_option autoImplicit false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

universe u

namespace E44

theorem finite_of_exact {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : B →+ C) (hfg : Function.Exact f g) [Finite A] [Finite C] : Finite B := by
  classical
  have hker : g.ker = f.range := hfg.addMonoidHom_ker_eq
  haveI : Finite f.range := Finite.of_surjective _ (AddMonoidHom.rangeRestrict_surjective f)
  haveI : Finite g.ker := by rw [hker]; infer_instance
  haveI : Finite g.range := inferInstance
  haveI : Finite (B ⧸ g.ker) := Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange g).symm.toEquiv
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker
  refine Nat.finite_of_card_ne_zero ?_
  rw [hcard]
  exact mul_ne_zero (Nat.card_pos (α := B ⧸ g.ker)).ne' (Nat.card_pos (α := g.ker)).ne'

end E44

theorem solution
    (S : Scheme.{u}) {X : ShortComplex (Sheaf (smallFppfTopology S) Ab.{u + 1})}
    (hX : X.ShortExact) (n : ℕ)
    (h₁ : Finite (fppfCohomology S X.X₁ n)) (h₃ : Finite (fppfCohomology S X.X₃ n)) :
    Finite (fppfCohomology S X.X₂ n) := by
  have hex : Function.Exact (fppfCohomologyMap S X.f n) (fppfCohomologyMap S X.g n) :=
    FppfCohomologyLES.cohomology_exact_two hX n
  exact E44.finite_of_exact _ _ hex
