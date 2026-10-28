import Decoupling.YonedaPushout

/-!
# Fixed-endpoint equivalence of literal two-extensions

The relation in Appendix D is the equivalence closure of actual commuting
middle maps, with both endpoints fixed.  The intermediate image module is
recorded through two short exact sequences; a map on that image is derived
from the two middle maps and is not an additional hypothesis.
-/

namespace Decoupling.YonedaZigzag

open CategoryTheory CategoryTheory.Abelian

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {A : Type} [CommRing A] (E B : ModuleCat.{0} A)

/-- An actual two-extension with specified endpoints and its image factor. -/
structure TwoExtension where
  N : ModuleCat.{0} A
  L : ModuleCat.{0} A
  Q : ModuleCat.{0} A
  i : E ⟶ N
  π : N ⟶ L
  j : L ⟶ Q
  p : Q ⟶ B
  iπ : i ≫ π = 0
  jp : j ≫ p = 0
  first_exact : (ShortComplex.mk i π iπ).ShortExact
  second_exact : (ShortComplex.mk j p jp).ShortExact

namespace TwoExtension

variable {E B} (X Y : TwoExtension E B)

def first : ShortComplex (ModuleCat A) := ShortComplex.mk X.i X.π X.iπ
def second : ShortComplex (ModuleCat A) := ShortComplex.mk X.j X.p X.jp
def δ : X.N ⟶ X.Q := X.π ≫ X.j
def extClass : Ext B E 2 := X.second_exact.extClass.comp X.first_exact.extClass
  (by decide : 1 + 1 = 2)

/-- Only the two middle maps are data; the endpoints are literally identities. -/
structure Hom where
  α₁ : X.N ⟶ Y.N
  α₀ : X.Q ⟶ Y.Q
  left : X.i ≫ α₁ = Y.i
  middle : α₁ ≫ Y.δ = X.δ ≫ α₀
  right : α₀ ≫ Y.p = X.p

namespace Hom

variable {X Y} (h : Hom X Y)

/-- Exactness determines the map on the intermediate image. -/
def imageMap : X.L ⟶ Y.L := by
  let : Epi X.π := X.first_exact.epi_g
  exact X.first_exact.exact.desc (h.α₁ ≫ Y.π) (by
    rw [← Category.assoc, h.left]
    exact Y.iπ)

theorem imageMap_left : X.π ≫ h.imageMap = h.α₁ ≫ Y.π := by
  let : Epi X.π := X.first_exact.epi_g
  exact X.first_exact.exact.g_desc _ _

theorem imageMap_right : h.imageMap ≫ Y.j = X.j ≫ h.α₀ := by
  let : Epi X.π := X.first_exact.epi_g
  apply (cancel_epi X.π).mp
  rw [← Category.assoc, h.imageMap_left, Category.assoc]
  exact h.middle

include h in
/-- A fixed-endpoint arrow preserves the actual derived Ext class. -/
theorem class_eq : X.extClass = Y.extClass :=
  YonedaCocycle.fixed_endpoint_invariance X.first_exact X.second_exact
    Y.first_exact Y.second_exact h.α₁ h.imageMap h.α₀ h.left.symm
    h.imageMap_left.symm h.imageMap_right h.right

end Hom

/-- The manuscript's equivalence relation: finite zigzags of fixed-endpoint maps. -/
def Equivalent : TwoExtension E B → TwoExtension E B → Prop :=
  Relation.EqvGen (fun X Y => Nonempty (Hom X Y))

theorem class_eq_of_equivalent (h : Equivalent X Y) : X.extClass = Y.extClass := by
  induction h with
  | rel X Y h => exact (Classical.choice h).class_eq
  | refl X => rfl
  | symm X Y _ ih => exact ih.symm
  | trans X Y Z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The literal zero extension `E --id→ E --0→ B --id→ B`. -/
def trivial (E B : ModuleCat.{0} A) : TwoExtension E B where
  N := E
  L := ModuleCat.of A (Fin 0 → A)
  Q := B
  i := 𝟙 E
  π := 0
  j := 0
  p := 𝟙 B
  iπ := by simp
  jp := by simp
  first_exact := {
    exact := (ShortComplex.moduleCat_exact_iff _).mpr (by
      intro e _
      exact ⟨e, rfl⟩)
    mono_f := inferInstance
    epi_g := (ModuleCat.epi_iff_surjective _).mpr (by
      intro z
      exact ⟨0, Subsingleton.elim _ _⟩)
  }
  second_exact := {
    exact := (ShortComplex.moduleCat_exact_iff _).mpr (by
      intro b hb
      exact ⟨0, hb.symm⟩)
    mono_f := (ModuleCat.mono_iff_injective _).mpr (by
      intro x y _
      exact Subsingleton.elim _ _)
    epi_g := inferInstance
  }

theorem trivial_class : (trivial E B).extClass = 0 := by
  have hz : (trivial E B).second_exact.extClass = 0 :=
    (ExtSplitting.extClass_zero_iff_section (trivial E B).second_exact).mpr
      ⟨𝟙 B, by simp [trivial]⟩
  rw [extClass, hz, Ext.zero_comp]

end TwoExtension

section LiteralModels

open TwoExtension

variable [CharP A 2] {E B}
variable {P₀ P₁ : Type} [AddCommGroup P₀] [Module A P₀]
  [AddCommGroup P₁] [Module A P₁]
variable (a₁ : P₁ →ₗ[A] P₀) (f : LinearMap.ker a₁ →ₗ[A] E)
variable (ε : P₀ →ₗ[A] B) (hexact : LinearMap.range a₁ = LinearMap.ker ε)
variable (hsurj : Function.Surjective ε)

/-- Package precisely the two literal pushout rows from Appendix D. -/
def model : TwoExtension E B where
  N := ModuleCat.of A (YonedaPushout.W a₁ f)
  L := ModuleCat.of A (LinearMap.range a₁)
  Q := ModuleCat.of A P₀
  i := ModuleCat.ofHom (YonedaPushout.ι a₁ f)
  π := ModuleCat.ofHom (YonedaPushout.δRange a₁ f)
  j := ModuleCat.ofHom (LinearMap.range a₁).subtype
  p := ModuleCat.ofHom ε
  iπ := (YonedaPushout.first a₁ f).zero
  jp := (YonedaPushout.second a₁ ε hexact).zero
  first_exact := YonedaPushout.first_shortExact a₁ f
  second_exact := YonedaPushout.second_shortExact a₁ ε hexact hsurj

theorem model_class : (model a₁ f ε hexact hsurj).extClass =
    YonedaPushout.extClass a₁ f ε hexact hsurj := rfl

variable (X : TwoExtension E B)
variable (q₁ : P₁ →ₗ[A] X.N) (q₀ : P₀ →ₗ[A] X.Q)
variable (hf : X.i.hom.comp f = q₁.comp (LinearMap.ker a₁).subtype)
variable (h₁ : X.δ.hom.comp q₁ = q₀.comp a₁) (h₀ : X.p.hom.comp q₀ = ε)

/-- The universal Φ_f is a morphism in the actual fixed-endpoint relation. -/
def modelMap : Hom (model a₁ f ε hexact hsurj) X := by
  have hδi : X.δ.hom.comp X.i.hom = 0 := by
    apply ModuleCat.hom_ext_iff.mp
    change X.i ≫ (X.π ≫ X.j) = 0
    rw [← Category.assoc, X.iπ, Limits.zero_comp]
  obtain ⟨hi, hd, _⟩ := YonedaPushout.fixed_endpoint_squares
    a₁ f ε X.i.hom X.δ.hom X.p.hom q₁ q₀ hf hδi h₁ h₀
  exact {
    α₁ := ModuleCat.ofHom (YonedaPushout.desc a₁ f X.i.hom q₁ hf)
    α₀ := ModuleCat.ofHom q₀
    left := ModuleCat.hom_ext hi
    middle := ModuleCat.hom_ext hd
    right := ModuleCat.hom_ext h₀
  }

/-- The literal Ψ_h defines a fixed-endpoint arrow between the pushout models. -/
def coboundaryMap (h : P₁ →ₗ[A] E) (g : LinearMap.ker a₁ →ₗ[A] E)
    (hfg : f + h.comp (LinearMap.ker a₁).subtype = g) :
    Hom (model a₁ f ε hexact hsurj) (model a₁ g ε hexact hsurj) where
  α₁ := ModuleCat.ofHom (YonedaPushout.coboundaryEquiv a₁ f h g hfg).toLinearMap
  α₀ := 𝟙 _
  left := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact YonedaPushout.coboundaryEquiv_ι a₁ f h g hfg
  middle := ModuleCat.hom_ext (YonedaPushout.δ_coboundaryEquiv a₁ f h g hfg)
  right := Category.id_comp _

/-- The second literal arrow in the diagram: `(pr₁,ε):E₀→T₀`. -/
def zeroModelMap : Hom (model a₁ (0 : LinearMap.ker a₁ →ₗ[A] E) ε hexact hsurj)
    (trivial E B) where
  α₁ := ModuleCat.ofHom (YonedaPushout.zeroProjection a₁)
  α₀ := ModuleCat.ofHom ε
  left := ModuleCat.hom_ext (YonedaPushout.zero_endpoint_squares a₁ ε hexact).1
  middle := by
    have hz := (YonedaPushout.zero_endpoint_squares (E := E) a₁ ε hexact).2
    apply ModuleCat.hom_ext
    exact hz.symm
  right := Category.comp_id _

/-- The full Appendix D criterion for the literal pushout and actual zigzags. -/
theorem model_equivalent_trivial_iff [Module.Projective A P₀] :
    Equivalent (model a₁ f ε hexact hsurj) (trivial E B) ↔
      ∃ h : P₁ →ₗ[A] E, h.comp (LinearMap.ker a₁).subtype = f := by
  constructor
  · intro heq
    apply (YonedaPushout.extClass_zero_iff a₁ f ε hexact hsurj).mp
    exact (class_eq_of_equivalent _ _ heq).trans (trivial_class (E := E) (B := B))
  · rintro ⟨h, hh⟩
    have hf0 : f + h.comp (LinearMap.ker a₁).subtype = 0 := by
      rw [hh]
      apply LinearMap.ext
      intro z
      exact Comparison.module_add_self (A := A) E (f z)
    exact Relation.EqvGen.trans _ _ _
      (.rel _ _ ⟨coboundaryMap a₁ f ε hexact hsurj h 0 hf0⟩)
      (.rel _ _ ⟨zeroModelMap a₁ ε hexact hsurj⟩)

include hf h₁ h₀ hexact hsurj in
/-- Necessity and sufficiency for any extension equipped with the comparison
in Appendix D.  The left side is now the literal fixed-endpoint relation. -/
theorem equivalent_trivial_iff_syzygy [Module.Projective A P₀] :
    Equivalent X (trivial E B) ↔
      ∃ h : P₁ →ₗ[A] E, h.comp (LinearMap.ker a₁).subtype = f := by
  have hmap : Equivalent (model a₁ f ε hexact hsurj) X :=
    .rel _ _ ⟨modelMap a₁ f ε hexact hsurj X q₁ q₀ hf h₁ h₀⟩
  constructor
  · intro heq
    exact (model_equivalent_trivial_iff a₁ f ε hexact hsurj).mp
      (.trans _ _ _ hmap heq)
  · intro hcob
    exact .trans _ _ _ (.symm _ _ hmap)
      ((model_equivalent_trivial_iff a₁ f ε hexact hsurj).mpr hcob)

end LiteralModels

section DegreeTwoComponent

open TwoExtension

variable [CharP A 2] {E B}
variable {P₀ P₁ P₂ : Type} [AddCommGroup P₀] [Module A P₀]
  [AddCommGroup P₁] [Module A P₁] [AddCommGroup P₂] [Module A P₂]
variable (X : TwoExtension E B)
variable (a₁ : P₁ →ₗ[A] P₀) (q₁ : P₁ →ₗ[A] X.N) (q₀ : P₀ →ₗ[A] X.Q)
variable (h₁ : X.δ.hom.comp q₁ = q₀.comp a₁)

omit [CharP A 2] in
include h₁ in
/-- The comparison restricts to a unique actual map out of `ker a₁`. -/
theorem exists_syzygy_map : ∃ f : LinearMap.ker a₁ →ₗ[A] E,
    X.i.hom.comp f = q₁.comp (LinearMap.ker a₁).subtype := by
  let : Mono X.j := X.second_exact.mono_f
  let : Mono X.i := X.first_exact.mono_f
  let k := ModuleCat.ofHom (q₁.comp (LinearMap.ker a₁).subtype)
  have hk : k ≫ X.π = 0 := by
    apply (cancel_mono X.j).mp
    rw [Limits.zero_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change X.δ.hom (q₁ z.val) = 0
    rw [show X.δ.hom (q₁ z.val) = q₀ (a₁ z.val) from DFunLike.congr_fun h₁ z.val,
      z.property, map_zero]
  exact ⟨(X.first_exact.exact.lift k hk).hom,
    ModuleCat.hom_ext_iff.mp (X.first_exact.exact.lift_f k hk)⟩

variable (a₂ : P₂ →ₗ[A] P₁) (exact21 : LinearMap.range a₂ = LinearMap.ker a₁)
variable (ε : P₀ →ₗ[A] B) (exact10 : LinearMap.range a₁ = LinearMap.ker ε)
variable (surjectiveε : Function.Surjective ε)
variable (f₂ : P₂ →ₗ[A] E)
variable (h₂ : X.i.hom.comp f₂ = q₁.comp a₂) (h₀ : X.p.hom.comp q₀ = ε)

include h₁ h₂ h₀ exact21 exact10 surjectiveε in
/-- Proposition D.1 with the literal finite-zigzag relation and the printed
degree-two condition `f₂ = h a₂`.  Projectivity is needed only in degree zero. -/
theorem equivalent_trivial_iff_component [Module.Projective A P₀] :
    Equivalent X (trivial E B) ↔ ∃ h : P₁ →ₗ[A] E, h.comp a₂ = f₂ := by
  obtain ⟨f, hf⟩ := exists_syzygy_map X a₁ q₁ q₀ h₁
  have hi : Function.Injective X.i.hom :=
    (ModuleCat.mono_iff_injective X.i).mp X.first_exact.mono_f
  have hcomp : f.comp (YonedaPushout.toKernel a₁ a₂ exact21) = f₂ := by
    apply LinearMap.ext
    intro z
    apply hi
    exact (DFunLike.congr_fun hf (YonedaPushout.toKernel a₁ a₂ exact21 z)).trans
      (DFunLike.congr_fun h₂ z).symm
  rw [equivalent_trivial_iff_syzygy a₁ f ε exact10 surjectiveε X q₁ q₀ hf h₁ h₀]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_⟩
    apply LinearMap.ext
    intro z
    exact (DFunLike.congr_fun hh (YonedaPushout.toKernel a₁ a₂ exact21 z)).trans
      (DFunLike.congr_fun hcomp z)
  · rintro ⟨h, hh⟩
    refine ⟨h, ?_⟩
    apply LinearMap.ext
    intro z
    obtain ⟨y, rfl⟩ := YonedaPushout.toKernel_surjective a₁ a₂ exact21 z
    exact (DFunLike.congr_fun hh y).trans (DFunLike.congr_fun hcomp y).symm

end DegreeTwoComponent

section Classification

open TwoExtension

variable [CharP A 2] {E B}
variable {P₀ P₁ : Type} [AddCommGroup P₀] [Module A P₀]
  [AddCommGroup P₁] [Module A P₁]
variable (a₁ : P₁ →ₗ[A] P₀) (ε : P₀ →ₗ[A] B)
variable (hexact : LinearMap.range a₁ = LinearMap.ker ε)
variable (hsurj : Function.Surjective ε)
variable [Module.Projective A P₀] [Module.Projective A P₁]

omit [CharP A 2] in
include hexact in
/-- Every two-extension admits the comparison used in Appendix D.  Neither
the comparison maps nor a pushout representative are assumed as inputs. -/
theorem exists_comparison (X : TwoExtension E B) :
    ∃ (q₀ : P₀ →ₗ[A] X.Q) (q₁ : P₁ →ₗ[A] X.N)
      (f : LinearMap.ker a₁ →ₗ[A] E),
      X.p.hom.comp q₀ = ε ∧ X.δ.hom.comp q₁ = q₀.comp a₁ ∧
      X.i.hom.comp f = q₁.comp (LinearMap.ker a₁).subtype := by
  have hp : Function.Surjective X.p.hom :=
    (ModuleCat.epi_iff_surjective X.p).mp X.second_exact.epi_g
  have hπ : Function.Surjective X.π.hom :=
    (ModuleCat.epi_iff_surjective X.π).mp X.first_exact.epi_g
  have hδ : LinearMap.range X.δ.hom = LinearMap.ker X.p.hom := by
    apply Submodule.ext
    intro z
    constructor
    · rintro ⟨n, rfl⟩
      exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp X.jp) (X.π.hom n)
    · intro hz
      obtain ⟨l, hl⟩ := (ShortComplex.moduleCat_exact_iff _).mp X.second_exact.exact z hz
      obtain ⟨n, hn⟩ := hπ l
      refine ⟨n, ?_⟩
      change X.j.hom (X.π.hom n) = z
      rw [hn]
      exact hl
  obtain ⟨q₀, h₀⟩ := Module.projective_lifting_property X.p.hom ε hp
  have hzero : X.p.hom.comp (q₀.comp a₁) = 0 := by
    apply LinearMap.ext
    intro z
    have hz : a₁ z ∈ LinearMap.ker ε := by rw [← hexact]; exact ⟨z, rfl⟩
    exact (DFunLike.congr_fun h₀ (a₁ z)).trans hz
  obtain ⟨q₁, h₁⟩ := Comparison.exists_lift_of_comp_eq_zero
    X.δ.hom X.p.hom (q₀.comp a₁) hδ hzero
  obtain ⟨f, hf⟩ := exists_syzygy_map X a₁ q₁ q₀ h₁
  exact ⟨q₀, q₁, f, h₀, h₁, hf⟩

omit [Module.Projective A P₁] in
/-- Equality of genuine classes of literal pushouts is witnessed by an
actual fixed-endpoint Ψ_h arrow, hence by the manuscript's equivalence. -/
theorem model_equivalent_of_class_eq
    (f g : LinearMap.ker a₁ →ₗ[A] E)
    (heq : (model a₁ f ε hexact hsurj).extClass =
      (model a₁ g ε hexact hsurj).extClass) :
    Equivalent (model a₁ f ε hexact hsurj) (model a₁ g ε hexact hsurj) := by
  let : Projective (YonedaPushout.second a₁ ε hexact).X₂ :=
    inferInstanceAs (Projective (ModuleCat.of A P₀))
  have hclasses := heq
  rw [model_class, model_class, YonedaPushout.extClass_eq_cocycleClass,
    YonedaPushout.extClass_eq_cocycleClass] at hclasses
  obtain ⟨h, hh⟩ := (YonedaCocycle.cocycleClass_eq_iff
    (YonedaPushout.second_shortExact a₁ ε hexact hsurj)
    (YonedaPushout.syzygy_shortExact a₁) (ModuleCat.ofHom f) (ModuleCat.ofHom g)).mp hclasses
  have hfg : f + h.hom.comp (LinearMap.ker a₁).subtype = g := by
    apply LinearMap.ext
    intro z
    have hh' := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hh) z
    change h.hom z.val = f z - g z at hh'
    change f z + h.hom z.val = g z
    rw [hh', sub_eq_add_neg, ← add_assoc,
      Comparison.module_add_self (A := A) E (f z), zero_add]
    exact neg_eq_of_add_eq_zero_left (Comparison.module_add_self (A := A) E (g z))
  exact .rel _ _ ⟨coboundaryMap a₁ f ε hexact hsurj h.hom g hfg⟩

include a₁ ε hexact hsurj in
/-- The fixed-endpoint equivalence classes agree with genuine derived Ext
equality.  This is a proved statement about `EqvGen`, not a definition of it. -/
theorem equivalent_iff_class_eq (X Y : TwoExtension E B) :
    Equivalent X Y ↔ X.extClass = Y.extClass := by
  constructor
  · exact class_eq_of_equivalent X Y
  · intro heq
    obtain ⟨qx₀, qx₁, f, hx₀, hx₁, hxf⟩ := exists_comparison a₁ ε hexact X
    obtain ⟨qy₀, qy₁, g, hy₀, hy₁, hyg⟩ := exists_comparison a₁ ε hexact Y
    let mx := modelMap a₁ f ε hexact hsurj X qx₁ qx₀ hxf hx₁ hx₀
    let my := modelMap a₁ g ε hexact hsurj Y qy₁ qy₀ hyg hy₁ hy₀
    have hm : (model a₁ f ε hexact hsurj).extClass =
        (model a₁ g ε hexact hsurj).extClass :=
      mx.class_eq.trans (heq.trans my.class_eq.symm)
    exact .trans _ _ _ (.symm _ _ (.rel _ _ ⟨mx⟩))
      (.trans _ _ _ (model_equivalent_of_class_eq a₁ ε hexact hsurj f g hm)
        (.rel _ _ ⟨my⟩))

include a₁ ε hexact hsurj in
/-- In particular the entire fixed-endpoint zero-class assertion is literal. -/
theorem equivalent_trivial_iff_extClass_zero (X : TwoExtension E B) :
    Equivalent X (trivial E B) ↔ X.extClass = 0 := by
  rw [equivalent_iff_class_eq a₁ ε hexact hsurj, trivial_class]

/-- Every genuine Ext² element is represented by a literal pushout. -/
theorem exists_model_class (e : Ext B E 2) :
    ∃ f : LinearMap.ker a₁ →ₗ[A] E, (model a₁ f ε hexact hsurj).extClass = e := by
  let : Projective (YonedaPushout.second a₁ ε hexact).X₂ :=
    inferInstanceAs (Projective (ModuleCat.of A P₀))
  let eclass := YonedaCocycle.cocycleQuotientEquiv
    (YonedaPushout.second_shortExact a₁ ε hexact hsurj)
    (YonedaPushout.syzygy_shortExact a₁) A E
  obtain ⟨f, hf⟩ := (LinearMap.range
    (ExtCokernel.homRestriction A (YonedaPushout.syzygy a₁) E)).mkQ_surjective (eclass.symm e)
  refine ⟨f.hom, ?_⟩
  rw [model_class, YonedaPushout.extClass_eq_cocycleClass,
    ← YonedaCocycle.cocycleQuotientEquiv_mk
      (YonedaPushout.second_shortExact a₁ ε hexact hsurj)
      (YonedaPushout.syzygy_shortExact a₁) A (ModuleCat.ofHom f.hom)]
  change eclass (Submodule.Quotient.mk f) = e
  exact (congrArg eclass hf).trans (eclass.apply_symm_apply e)

/-- The quotient is by literal fixed-endpoint zigzags, independently of Ext. -/
def fixedEndpointSetoid : Setoid (TwoExtension E B) where
  r := Equivalent
  iseqv := Relation.EqvGen.is_equivalence _

/-- Send a fixed-endpoint extension class to its genuine Yoneda splice. -/
def classMap : Quotient (fixedEndpointSetoid (E := E) (B := B)) → Ext B E 2 :=
  Quotient.lift TwoExtension.extClass (fun X Y h => class_eq_of_equivalent X Y h)

include a₁ ε hexact hsurj in
theorem classMap_bijective : Function.Bijective (classMap (E := E) (B := B)) := by
  constructor
  · intro x y hxy
    obtain ⟨X, rfl⟩ := Quotient.exists_rep x
    obtain ⟨Y, rfl⟩ := Quotient.exists_rep y
    exact Quotient.sound ((equivalent_iff_class_eq a₁ ε hexact hsurj X Y).mpr hxy)
  · intro e
    obtain ⟨f, hf⟩ := exists_model_class a₁ ε hexact hsurj e
    exact ⟨Quotient.mk _ (model a₁ f ε hexact hsurj), hf⟩

/-- The explicit fixed-endpoint quotient and genuine Ext² are bijective.
The map is the actual splice class, not an arbitrary chosen bijection. -/
def fixedEndpointEquivExt :
    Quotient (fixedEndpointSetoid (E := E) (B := B)) ≃ Ext B E 2 :=
  Equiv.ofBijective classMap (classMap_bijective a₁ ε hexact hsurj)

@[simp] theorem fixedEndpointEquivExt_apply (X : TwoExtension E B) :
    fixedEndpointEquivExt a₁ ε hexact hsurj (Quotient.mk _ X) = X.extClass := rfl

end Classification

end
end Decoupling.YonedaZigzag
