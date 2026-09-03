import Mathlib
import P2M.Util
namespace P2MW.S_Algebra_exists_monoidHom_algebraMap_eq_norm_of_isIntegrallyClosed

set_option autoImplicit false

universe u v w w'

theorem solution
    {A : Type u} {B : Type v} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B]
    (K : Type w) (L : Type w') [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] :
    ∃ N : B →* A, ∀ b : B, algebraMap A K (N b) = Algebra.norm K (algebraMap B L b) := by
  classical

  have hmem : ∀ b : B, ∃ a : A, algebraMap A K a = Algebra.norm K (algebraMap B L b) := by
    intro b
    have hb : IsIntegral A (algebraMap B L b) := (Algebra.IsIntegral.isIntegral (R := A) b).algebraMap
    have hn : IsIntegral A (Algebra.norm K (algebraMap B L b)) := Algebra.isIntegral_norm K hb
    exact IsIntegrallyClosed.isIntegral_iff.mp hn
  choose N hN using hmem
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  refine ⟨{ toFun := N, map_one' := ?_, map_mul' := ?_ }, fun b => hN b⟩
  · apply hinj
    rw [hN, map_one, map_one, map_one]
  · intro b c
    apply hinj
    rw [hN, map_mul, map_mul, map_mul, hN, hN]
