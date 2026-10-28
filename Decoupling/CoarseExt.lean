import Decoupling.CoarseCSS
import Decoupling.ScalarRestriction

/-!
# Genuine Ext layers of the expanded CSS presentation

The layers on the coarse side are derived Ext of the expanded check matrix.
Their equivalences with the restricted original layers are proved through the
actual physical free resolution and its cycle/cokernel quotients.
-/

namespace Decoupling.CoarseExt

open CategoryTheory CategoryTheory.Abelian GeneralRetained ResolutionExt Matrix

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

section CochainEquivalence

universe u
variable {A : Type u} [CommRing A]
  {P F Q P' F' Q' : Type u}
  [AddCommGroup P] [Module A P] [AddCommGroup F] [Module A F]
  [AddCommGroup Q] [Module A Q] [AddCommGroup P'] [Module A P']
  [AddCommGroup F'] [Module A F'] [AddCommGroup Q'] [Module A Q']

/-- A coordinate change of the entire physical dual cochain. -/
structure CochainEquiv (c : Syndrome.Cochain A P F Q) (d : Syndrome.Cochain A P' F' Q') where
  eP : P ≃ₗ[A] P'
  eF : F ≃ₗ[A] F'
  eQ : Q ≃ₗ[A] Q'
  comm₁ : ∀ p, d.d₁ (eP p) = eF (c.d₁ p)
  comm₂ : ∀ f, d.γ (eF f) = eQ (c.γ f)

private theorem range_map_eq {V W V' W' : Type u}
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    [AddCommGroup V'] [Module A V'] [AddCommGroup W'] [Module A W']
    (f : V →ₗ[A] W) (g : V' →ₗ[A] W') (eV : V ≃ₗ[A] V') (eW : W ≃ₗ[A] W')
    (h : ∀ v, g (eV v) = eW (f v)) :
    (LinearMap.range f).map eW.toLinearMap = LinearMap.range g := by
  ext w
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨eV v, h v⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨v, rfl⟩ := eV.surjective v
    exact ⟨f v, ⟨v, rfl⟩, (h v).symm⟩

namespace CochainEquiv
variable {c : Syndrome.Cochain A P F Q} {d : Syndrome.Cochain A P' F' Q'}
  (e : CochainEquiv c d)

def cycles : LinearMap.ker c.γ ≃ₗ[A] LinearMap.ker d.γ where
  toFun f := ⟨e.eF f, by rw [LinearMap.mem_ker, e.comm₂, f.property, map_zero]⟩
  invFun f := ⟨e.eF.symm f, by
    apply e.eQ.injective
    rw [map_zero, ← e.comm₂, e.eF.apply_symm_apply]
    exact f.property⟩
  left_inv f := by apply Subtype.ext; exact e.eF.symm_apply_apply f
  right_inv f := by apply Subtype.ext; exact e.eF.apply_symm_apply f
  map_add' _ _ := by apply Subtype.ext; exact e.eF.map_add _ _
  map_smul' _ _ := by apply Subtype.ext; exact e.eF.map_smul _ _

def symm : CochainEquiv d c where
  eP := e.eP.symm
  eF := e.eF.symm
  eQ := e.eQ.symm
  comm₁ p := by
    apply e.eF.injective
    simpa using (e.comm₁ (e.eP.symm p)).symm
  comm₂ f := by
    apply e.eQ.injective
    simpa using (e.comm₂ (e.eF.symm f)).symm

def LEquiv : c.L ≃ₗ[A] d.L where
  toFun l := ⟨e.eQ l, by
    obtain ⟨f, hf⟩ := l.property
    exact ⟨e.eF f, (e.comm₂ f).trans (congrArg e.eQ hf)⟩⟩
  invFun l := ⟨e.eQ.symm l, by
    obtain ⟨f, hf⟩ := l.property
    refine ⟨e.eF.symm f, e.eQ.injective ?_⟩
    rw [← e.comm₂, e.eF.apply_symm_apply, e.eQ.apply_symm_apply]
    exact hf⟩
  left_inv l := by apply Subtype.ext; exact e.eQ.symm_apply_apply l
  right_inv l := by apply Subtype.ext; exact e.eQ.apply_symm_apply l
  map_add' _ _ := by apply Subtype.ext; exact e.eQ.map_add _ _
  map_smul' _ _ := by apply Subtype.ext; exact e.eQ.map_smul _ _

def NEquiv : c.N ≃ₗ[A] d.N :=
  Submodule.Quotient.equiv _ _ e.eF (range_map_eq _ _ e.eP e.eF e.comm₁)

def C1Equiv : c.C1 ≃ₗ[A] d.C1 :=
  Submodule.Quotient.equiv _ _ e.cycles (range_map_eq _ _ e.eP e.cycles (fun p => by
    apply Subtype.ext
    exact e.comm₁ p))

def C2Equiv : c.C2 ≃ₗ[A] d.C2 :=
  Submodule.Quotient.equiv _ _ e.eQ (range_map_eq _ _ e.eF e.eQ e.comm₂)

@[simp] theorem NEquiv_mk (f : F) : e.NEquiv (c.ε f) = d.ε (e.eF f) := rfl
@[simp] theorem C1Equiv_mk (f : LinearMap.ker c.γ) :
    e.C1Equiv (Submodule.Quotient.mk f) = Submodule.Quotient.mk (e.cycles f) := rfl
@[simp] theorem C2Equiv_mk (q : Q) : e.C2Equiv (c.pQ q) = d.pQ (e.eQ q) := rfl

theorem NEquiv_ι (a : c.C1) : e.NEquiv (c.ι a) = d.ι (e.C1Equiv a) := by
  induction a using Submodule.Quotient.induction_on
  rfl

theorem LEquiv_π (a : c.N) : e.LEquiv (c.π a) = d.π (e.NEquiv a) := by
  induction a using Submodule.Quotient.induction_on with
  | H f =>
    apply Subtype.ext
    exact (e.comm₂ f).symm

def firstMap : c.first ⟶ d.first where
  τ₁ := e.C1Equiv.toModuleIso.hom
  τ₂ := e.NEquiv.toModuleIso.hom
  τ₃ := e.LEquiv.toModuleIso.hom
  comm₁₂ := ModuleCat.hom_ext (LinearMap.ext (fun a => (e.NEquiv_ι a).symm))
  comm₂₃ := ModuleCat.hom_ext (LinearMap.ext (fun a => (e.LEquiv_π a).symm))

def secondMap : c.second ⟶ d.second where
  τ₁ := e.LEquiv.toModuleIso.hom
  τ₂ := e.eQ.toModuleIso.hom
  τ₃ := e.C2Equiv.toModuleIso.hom
  comm₁₂ := by rfl
  comm₂₃ := by rfl

/-- Naturality of the actual two-extension, including both endpoint identifications. -/
theorem κ_naturality :
    c.κ.comp (Ext.mk₀ e.C1Equiv.toModuleIso.hom) (add_zero 2) =
      (Ext.mk₀ e.C2Equiv.toModuleIso.hom).comp d.κ (zero_add 2) := by
  have h₁ := c.first_shortExact.extClass_naturality d.first_shortExact e.firstMap
  have h₂ := c.second_shortExact.extClass_naturality d.second_shortExact e.secondMap
  change c.first_shortExact.extClass.comp (Ext.mk₀ e.C1Equiv.toModuleIso.hom) _ =
    (Ext.mk₀ e.LEquiv.toModuleIso.hom).comp d.first_shortExact.extClass _ at h₁
  change c.second_shortExact.extClass.comp (Ext.mk₀ e.LEquiv.toModuleIso.hom) _ =
    (Ext.mk₀ e.C2Equiv.toModuleIso.hom).comp d.second_shortExact.extClass _ at h₂
  unfold Syndrome.Cochain.κ
  rw [Ext.comp_assoc_of_third_deg_zero, h₁,
    ← Ext.comp_assoc_of_second_deg_zero, h₂]
  exact Ext.comp_assoc _ _ _ _ _ (by decide)

/-- Explicit source/target transport formula for the genuine obstruction. -/
theorem κ_transport :
    (Ext.mk₀ e.C2Equiv.toModuleIso.inv).comp
      (c.κ.comp (Ext.mk₀ e.C1Equiv.toModuleIso.hom) (add_zero 2)) (zero_add 2) = d.κ := by
  rw [e.κ_naturality, Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id, Ext.mk₀_id_comp]

include e in
theorem κ_zero_of_zero (hc : c.κ = 0) : d.κ = 0 := by
  rw [← e.κ_transport, hc, Ext.zero_comp, Ext.comp_zero]

include e in
theorem κ_zero_iff : c.κ = 0 ↔ d.κ = 0 :=
  ⟨e.κ_zero_of_zero, e.symm.κ_zero_of_zero⟩

end CochainEquiv
end CochainEquivalence

section Restriction

variable (n : ℕ)
  {P F Q : Type} [AddCommGroup P] [Module R P]
  [AddCommGroup F] [Module R F] [AddCommGroup Q] [Module R Q]

abbrev Restrict (V : Type) [AddCommGroup V] [Module R V] :=
  RetainedLayers.restricted n (ModuleCat.of R V)

def restrictMap (f : P →ₗ[R] F) : Restrict n P →ₗ[R] Restrict n F where
  toFun := f
  map_add' := f.map_add
  map_smul' r v := f.map_smul (embed n r) v

def restrictEquiv (e : P ≃ₗ[R] F) : Restrict n P ≃ₗ[R] Restrict n F where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' r v := e.map_smul (embed n r) v

/-- Scalar restriction followed by the literal renaming of retained translations. -/
def restrictCochain (c : Syndrome.Cochain R P F Q) :
    Syndrome.Cochain R (Restrict n P) (Restrict n F) (Restrict n Q) where
  d₁ := restrictMap n c.d₁
  γ := restrictMap n c.γ
  square := by ext p; exact DFunLike.congr_fun c.square p

/-- The quotient relation is unchanged by restricting its scalar action. -/
def restrictC1Equiv (c : Syndrome.Cochain R P F Q) :
    (restrictCochain n c).C1 ≃ₗ[R] Restrict n c.C1 where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def restrictC2Equiv (c : Syndrome.Cochain R P F Q) :
    (restrictCochain n c).C2 ≃ₗ[R] Restrict n c.C2 where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Restriction

variable (n : ℕ) [NeZero n]
  {q s r cX : ℕ} {c : CSS.Checks q s r} (h : CSSResolution c cX)

/-- The physical cochain of the expanded checks, rather than a prescribed layer. -/
def cochainEquiv : CochainEquiv (restrictCochain n h.cochain)
    (CoarseCSS.resolution n h).cochain where
  eP := CoarseCSS.vectorEquiv n q
  eF := CoarseCSS.vectorEquiv n s
  eQ := CoarseCSS.vectorEquiv n cX
  comm₁ p := CoarseCSS.matrix_mulVec n c.H_X p
  comm₂ f := by
    change dagger (CoarseCSS.matrix n h.Γ) *ᵥ CoarseCSS.vector n f =
      CoarseCSS.vector n (dagger h.Γ *ᵥ f)
    rw [← CoarseCSS.matrix_dagger]
    exact CoarseCSS.matrix_mulVec n (dagger h.Γ) f

/-- Actual Ext¹ of the expanded CSS checks is the restricted original Ext¹. -/
def E1Equiv : ExtLayers.E_X (CoarseCSS.checks n c) 1 ≃ₗ[R]
    RetainedLayers.restricted n (LayerTranslations.layer c 1) :=
  (CoarseCSS.resolution n h).C1EquivE_X.symm |>.trans
    (cochainEquiv n h).C1Equiv.symm |>.trans
    (restrictC1Equiv n h.cochain) |>.trans
    (restrictEquiv n h.C1EquivE_X)

/-- Actual Ext² of the expanded CSS checks is the restricted original Ext². -/
def E2Equiv : ExtLayers.E_X (CoarseCSS.checks n c) 2 ≃ₗ[R]
    RetainedLayers.restricted n (LayerTranslations.layer c 2) :=
  (CoarseCSS.resolution n h).C2EquivE_X.symm |>.trans
    (cochainEquiv n h).C2Equiv.symm |>.trans
    (restrictC2Equiv n h.cochain) |>.trans
    (restrictEquiv n h.C2EquivE_X)

/-- An R-linear equivalence restricts to the same coefficient field action. -/
def coefficientsEquiv {M N : ModuleCat R} (e : M ≃ₗ[R] N) :
    LayerTranslations.coefficients M ≃ₗ[ZMod 2] LayerTranslations.coefficients N where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' a x := e.map_smul (constant a) x

include h in
/-- The first finite layer has the identical coefficient dimension. -/
theorem E1_finrank :
    Module.finrank (ZMod 2) (LayerTranslations.coefficients
      (LayerTranslations.layer (CoarseCSS.checks n c) 1)) =
    Module.finrank (ZMod 2) (LayerTranslations.coefficients (LayerTranslations.layer c 1)) :=
  ((coefficientsEquiv (E1Equiv n h)).trans
    (RetainedLayers.coefficientEquiv n (LayerTranslations.layer c 1))).finrank_eq

include h in
theorem E2_finrank :
    Module.finrank (ZMod 2) (LayerTranslations.coefficients
      (LayerTranslations.layer (CoarseCSS.checks n c) 2)) =
    Module.finrank (ZMod 2) (LayerTranslations.coefficients (LayerTranslations.layer c 2)) :=
  ((coefficientsEquiv (E2Equiv n h)).trans
    (RetainedLayers.coefficientEquiv n (LayerTranslations.layer c 2))).finrank_eq

include h in
theorem E1_finite [FiniteDimensional (ZMod 2)
    (LayerTranslations.coefficients (LayerTranslations.layer c 1))] :
    FiniteDimensional (ZMod 2) (LayerTranslations.coefficients
      (LayerTranslations.layer (CoarseCSS.checks n c) 1)) :=
  Module.Finite.equiv ((coefficientsEquiv (E1Equiv n h)).trans
    (RetainedLayers.coefficientEquiv n (LayerTranslations.layer c 1))).symm

include h in
theorem E2_finite [FiniteDimensional (ZMod 2)
    (LayerTranslations.coefficients (LayerTranslations.layer c 2))] :
    FiniteDimensional (ZMod 2) (LayerTranslations.coefficients
      (LayerTranslations.layer (CoarseCSS.checks n c) 2)) :=
  Module.Finite.equiv ((coefficientsEquiv (E2Equiv n h)).trans
    (RetainedLayers.coefficientEquiv n (LayerTranslations.layer c 2))).symm

/-- The coarse obstruction is exactly the class of the restricted physical two-extension. -/
theorem κ_zero_iff_restricted :
    (CoarseCSS.resolution n h).cochain.κ = 0 ↔ (restrictCochain n h.cochain).κ = 0 :=
  (cochainEquiv n h).κ_zero_iff.symm

end
end Decoupling.CoarseExt
