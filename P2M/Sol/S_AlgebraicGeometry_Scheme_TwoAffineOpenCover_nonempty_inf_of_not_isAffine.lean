import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_inf_of_not_isAffine

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X : Scheme.{u}} [IrreducibleSpace X] (𝒱 : X.TwoAffineOpenCover) (hX : ¬ IsAffine X) :
    ((𝒱.U0 ⊓ 𝒱.U1 : X.Opens) : Set X).Nonempty := by

  have hne : ∀ {U V : X.Opens}, IsAffineOpen U → U ⊔ V = ⊤ → ((V : X.Opens) : Set X).Nonempty := by
    intro U V hU hUV
    rw [← TopologicalSpace.Opens.ne_bot_iff_nonempty]
    rintro rfl
    rw [sup_bot_eq] at hUV
    subst hUV
    exact hX (@IsAffine.of_isIso _ _ X.topIso.inv inferInstance hU)
  have h1 : ((𝒱.U1 : X.Opens) : Set X).Nonempty := hne 𝒱.isAffineOpen_U0 𝒱.sup_eq_top
  have h0 : ((𝒱.U0 : X.Opens) : Set X).Nonempty := hne 𝒱.isAffineOpen_U1 (by rw [sup_comm]; exact 𝒱.sup_eq_top)
  exact nonempty_preirreducible_inter 𝒱.U0.isOpen 𝒱.U1.isOpen h0 h1
