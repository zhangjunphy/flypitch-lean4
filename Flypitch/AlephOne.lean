import Flypitch.PSetOrdinal

universe u

namespace Flypitch

open Cardinal

/-!
`Flypitch.AlephOne` starts the forcing-side `aleph_one.lean` port. This first tranche keeps to the
pure `pSet` layer built on top of `Flypitch.PSetOrdinal`: regularity, the canonical `aleph_one`
pre-set, set-theoretic complement/intersection, and the basic ordinal-style comparison lemmas for
ordinal-shaped pre-sets.
-/

set_option linter.missingDocs false
set_option linter.style.longLine false

namespace pSet

/-- Every nonempty pre-set has an `∈`-minimal member. -/
theorem regularity (x : pSet.{u}) (hNonempty : ¬ PSet.Equiv x (∅ : pSet.{u})) :
    ∃ y : pSet.{u}, y ∈ x ∧ ∀ z, z ∈ x → z ∉ y := by
  classical
  have hxMem : ∃ y : pSet.{u}, y ∈ x := by
    by_contra hNo
    apply hNonempty
    apply (ext_iff).2
    intro z
    constructor
    · intro hz
      exact False.elim (hNo ⟨z, hz⟩)
    · intro hz
      exact False.elim (PSet.notMem_empty _ hz)
  have hxNonempty : x.Nonempty := by
    simpa [PSet.nonempty_def] using hxMem
  simpa using well_founded x hxNonempty

/-- The pre-set coding `aleph_1`. -/
noncomputable def aleph_one : pSet.{u} :=
  card_ex (Cardinal.aleph 1)

theorem aleph_one_Ord : Ord aleph_one := by
  simpa [aleph_one, card_ex] using Ord_mk (Cardinal.ord (Cardinal.aleph 1))

/-- A weak characterization of `aleph_one`: an ordinal admitting no injection into `omega` and
contained in every other such ordinal. -/
def aleph_one_weak_Ord_spec (x : pSet.{u}) : Prop :=
  Ord x ∧ ∀ y : pSet.{u}, Ord y ∧ ¬ injects_into y (PSet.omega : pSet.{u}) → x ⊆ y

/-- The trichotomy relation on members of a pre-set. -/
def epsilon_trichotomy (x : pSet.{u}) : Prop :=
  ∀ y : pSet.{u}, y ∈ x → ∀ z : pSet.{u}, z ∈ x → PSet.Equiv y z ∨ y ∈ z ∨ z ∈ y

theorem epsilon_trichotomy_of_Ord {x : pSet.{u}} (hOrd : Ord x) : epsilon_trichotomy x :=
  hOrd.1.1

theorem epsilon_trichotomy_of_Ord' {x : pSet.{u}} (hOrd : Ord x) {y : pSet.{u}} (hy : y ∈ x)
    {z : pSet.{u}} (hz : z ∈ x) : PSet.Equiv y z ∨ y ∈ z ∨ z ∈ y :=
  epsilon_trichotomy_of_Ord hOrd y hy z hz

theorem is_transitive_of_mem_Ord {x : pSet.{u}} (hOrd : Ord x) : is_transitive x :=
  is_transitive_of_Ord hOrd

theorem mem_of_mem_subset {x y z : pSet.{u}} (hSub : y ⊆ z) (hMem : x ∈ y) : x ∈ z :=
  all_mem_of_subset hSub x hMem

theorem mem_of_mem_Ord {x y z : pSet.{u}} (hOrd : Ord z) (hMem₁ : x ∈ y) (hMem₂ : y ∈ z) :
    x ∈ z :=
  mem_trans_of_transitive hMem₁ hMem₂ (is_transitive_of_Ord hOrd)

theorem subset_of_mem_Ord {x z : pSet.{u}} (hOrd : Ord z) (hMem : x ∈ z) : x ⊆ z :=
  is_transitive_of_Ord hOrd x hMem

theorem Ord_of_mem_Ord {x z : pSet.{u}} (hMem : x ∈ z) (hOrd : Ord z) : Ord x := by
  refine ⟨?_, transitive_of_mem_Ord hOrd hMem⟩
  constructor
  · intro y hy z' hz
    exact epsilon_trichotomy_of_Ord' hOrd
      (mem_of_mem_Ord hOrd hy hMem)
      (mem_of_mem_Ord hOrd hz hMem)
  · intro s _ hs
    exact well_founded s hs

/-- Relative complement inside a pre-set. -/
def compl (x y : pSet.{u}) : pSet.{u} :=
  PSet.sep (fun z => ¬ z ∈ y) x

theorem mem_compl_iff {x y z : pSet.{u}} : z ∈ compl x y ↔ z ∈ x ∧ ¬ z ∈ y := by
  simpa [compl] using
    (mem_sep_iff (x := x) (w := z) (p := fun w => ¬ w ∈ y)
      (hcongr := P_ext_neg (P_ext_mem_left (y := y))))

/-- Nonemptiness expressed as non-equivalence with the empty pre-set. -/
@[reducible] def non_empty (x : pSet.{u}) : Prop :=
  ¬ PSet.Equiv x (∅ : pSet.{u})

theorem equiv_unfold' {x y : pSet.{u}} :
    PSet.Equiv x y ↔ (∀ z, z ∈ x → z ∈ y) ∧ ∀ z, z ∈ y → z ∈ x := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro z hz
      exact (PSet.Mem.congr_right h).1 hz
    · intro z hz
      exact (PSet.Mem.congr_right h).2 hz
  · rintro ⟨hxy, hyx⟩
    exact (ext_iff).2 fun z => ⟨hxy z, hyx z⟩

theorem nonempty_iff_exists_mem {x : pSet.{u}} : non_empty x ↔ ∃ y : pSet.{u}, y ∈ x := by
  classical
  constructor
  · intro hx
    by_contra hNo
    apply hx
    apply (ext_iff).2
    intro z
    constructor
    · intro hz
      exact False.elim (hNo ⟨z, hz⟩)
    · intro hz
      exact False.elim (PSet.notMem_empty _ hz)
  · rintro ⟨y, hy⟩ hEq
    exact PSet.notMem_empty _ ((PSet.Mem.congr_right hEq).1 hy)

theorem nonempty_compl_of_ne {x y : pSet.{u}} (hNe : ¬ PSet.Equiv x y) :
    non_empty (compl x y) ∨ non_empty (compl y x) := by
  classical
  by_cases hxy : ∃ z : pSet.{u}, z ∈ x ∧ ¬ z ∈ y
  · left
    rw [nonempty_iff_exists_mem]
    rcases hxy with ⟨z, hz₁, hz₂⟩
    exact ⟨z, (mem_compl_iff).2 ⟨hz₁, hz₂⟩⟩
  · right
    rw [nonempty_iff_exists_mem]
    by_contra hNo
    apply hNe
    apply (ext_iff).2
    intro z
    constructor
    · intro hz
      by_contra hzNot
      exact hxy ⟨z, hz, hzNot⟩
    · intro hz
      by_contra hzNot
      exact hNo ⟨z, (mem_compl_iff).2 ⟨hz, hzNot⟩⟩

theorem compl_empty_of_subset {x y : pSet.{u}} (hSub : x ⊆ y) :
    PSet.Equiv (compl x y) (∅ : pSet.{u}) := by
  classical
  by_contra hContra
  change non_empty (compl x y) at hContra
  rcases (nonempty_iff_exists_mem).1 hContra with ⟨z, hz⟩
  rcases (mem_compl_iff).1 hz with ⟨hzx, hznoty⟩
  exact hznoty (mem_of_mem_subset hSub hzx)

/-- Binary intersection of pre-sets. -/
def binary_inter (x y : pSet.{u}) : pSet.{u} :=
  PSet.sep (fun z => z ∈ y) x

theorem mem_binary_inter_iff {x y z : pSet.{u}} :
    z ∈ binary_inter x y ↔ z ∈ x ∧ z ∈ y := by
  simpa [binary_inter] using
    (mem_sep_iff (x := x) (w := z) (p := fun w => w ∈ y)
      (hcongr := P_ext_mem_left (y := y)))

theorem binary_inter_subset {x y : pSet.{u}} :
    binary_inter x y ⊆ x ∧ binary_inter x y ⊆ y := by
  refine ⟨sep_subset (p := fun z => z ∈ y) (x := x), ?_⟩
  exact subset_of_all_mem fun z hz => (mem_binary_inter_iff).1 hz |>.2

theorem Ord_binary_inter {x y : pSet.{u}} (h₁ : Ord x) (h₂ : Ord y) :
    Ord (binary_inter x y) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro w hw z hz
      exact epsilon_trichotomy_of_Ord' h₁
        ((mem_binary_inter_iff).1 hw).1
        ((mem_binary_inter_iff).1 hz).1
    · intro s _ hs
      exact well_founded s hs
  · intro z hz
    rcases (mem_binary_inter_iff).1 hz with ⟨hzx, hzy⟩
    apply subset_of_all_mem
    intro w hw
    refine (mem_binary_inter_iff).2 ⟨?_, ?_⟩
    · exact mem_of_mem_Ord h₁ hw hzx
    · exact mem_of_mem_Ord h₂ hw hzy

theorem Ord.lt_of_ne_and_le {x y : pSet.{u}} (h₁ : Ord x) (h₂ : Ord y)
    (hNe : ¬ PSet.Equiv x y) (hLe : x ⊆ y) : x ∈ y := by
  classical
  have hComplNonempty : non_empty (compl y x) := by
    rcases nonempty_compl_of_ne hNe with hxy | hyx
    · exfalso
      exact hxy (compl_empty_of_subset hLe)
    · exact hyx
  rcases regularity (compl y x) hComplNonempty with ⟨z, hz, hzMin⟩
  rcases (mem_compl_iff).1 hz with ⟨hzY, hzNotX⟩
  have hEq : PSet.Equiv x z := by
    apply (ext_iff).2
    intro a
    constructor
    · intro haX
      have haY : a ∈ y := mem_of_mem_subset hLe haX
      rcases epsilon_trichotomy_of_Ord' h₂ haY hzY with hEq' | haZ | hzA
      · exact False.elim (hzNotX ((PSet.Mem.congr_left hEq').1 haX))
      · exact haZ
      · exact False.elim (hzNotX (mem_of_mem_Ord h₁ hzA haX))
    · intro haZ
      by_contra haNotX
      have haY : a ∈ y := mem_of_mem_Ord h₂ haZ hzY
      have haCompl : a ∈ compl y x := (mem_compl_iff).2 ⟨haY, haNotX⟩
      exact hzMin a haCompl haZ
  exact (PSet.Mem.congr_left hEq).2 hzY

theorem Ord.le_or_le {x y : pSet.{u}} (h₁ : Ord x) (h₂ : Ord y) : x ⊆ y ∨ y ⊆ x := by
  classical
  let w : pSet.{u} := binary_inter x y
  have hwOrd : Ord w := Ord_binary_inter h₁ h₂
  have hwEq : PSet.Equiv w x ∨ PSet.Equiv w y := by
    by_contra h
    have h' := not_or.mp h
    have hwx : w ∈ x := Ord.lt_of_ne_and_le hwOrd h₁ h'.1 (binary_inter_subset (x := x) (y := y)).1
    have hwy : w ∈ y := Ord.lt_of_ne_and_le hwOrd h₂ h'.2 (binary_inter_subset (x := x) (y := y)).2
    have hww : w ∈ w := (mem_binary_inter_iff).2 ⟨hwx, hwy⟩
    exact mem_self hww
  rcases hwEq with hEq | hEq
  · left
    exact (PSet.Subset.congr_left hEq).1 (binary_inter_subset (x := x) (y := y)).2
  · right
    exact (PSet.Subset.congr_left hEq).1 (binary_inter_subset (x := x) (y := y)).1

theorem equiv.comm {x y : pSet.{u}} : PSet.Equiv x y ↔ PSet.Equiv y x := by
  constructor <;> intro h <;> exact h.symm

theorem Ord.trichotomy {x y : pSet.{u}} (h₁ : Ord x) (h₂ : Ord y) :
    PSet.Equiv x y ∨ x ∈ y ∨ y ∈ x := by
  classical
  rcases Ord.le_or_le h₁ h₂ with hxy | hyx
  · by_cases hEq : PSet.Equiv x y
    · exact Or.inl hEq
    · exact Or.inr (Or.inl (Ord.lt_of_ne_and_le h₁ h₂ hEq hxy))
  · by_cases hEq : PSet.Equiv x y
    · exact Or.inl hEq
    · exact Or.inr (Or.inr (Ord.lt_of_ne_and_le h₂ h₁
        (by simpa [equiv.comm] using hEq) hyx))

theorem Ord.lt_of_le_of_lt {x y z : pSet.{u}} (hx : Ord x) (hy : Ord y) (hz : Ord z)
    (hLe : x ⊆ y) (hLt : y ∈ z) : x ∈ z := by
  rcases Ord.trichotomy hx hy with hEq | hxy | hyx
  · exact (PSet.Mem.congr_left hEq).2 hLt
  · exact mem_trans_of_transitive hxy hLt (is_transitive_of_Ord hz)
  · have hySub : y ⊆ x := subset_of_mem_Ord hx hyx
    have hEq' : PSet.Equiv x y := by
      apply (ext_iff).2
      intro a
      exact ⟨fun ha => all_mem_of_subset hLe a ha, fun ha => all_mem_of_subset hySub a ha⟩
    exact (PSet.Mem.congr_left hEq').2 hLt

theorem Ord.le_iff_lt_or_eq {x z : pSet.{u}} (h₁ : Ord x) (h₂ : Ord z) :
    x ⊆ z ↔ x ∈ z ∨ PSet.Equiv x z := by
  constructor
  · intro hLe
    by_cases hEq : PSet.Equiv x z
    · exact Or.inr hEq
    · exact Or.inl (Ord.lt_of_ne_and_le h₁ h₂ hEq hLe)
  · rintro (hLt | hEq)
    · exact subset_of_mem_Ord h₂ hLt
    · exact subset_of_all_mem fun a ha => (PSet.Mem.congr_right hEq).1 ha

noncomputable def ordOfMemMk {η : ordinal} (i : (ordinal.mk η).Type) : ordinal :=
  Classical.choose
    (equiv_mk_of_mem_mk (η := η) (x := (ordinal.mk η).Func i)
      (mem_mk' (x := ordinal.mk η) (i := i)))

theorem ordOfMemMk_lt {η : ordinal} (i : (ordinal.mk η).Type) : ordOfMemMk i < η :=
  (Classical.choose_spec
    (equiv_mk_of_mem_mk (η := η) (x := (ordinal.mk η).Func i)
      (mem_mk' (x := ordinal.mk η) (i := i)))).1

theorem func_equiv_ordOfMemMk {η : ordinal} (i : (ordinal.mk η).Type) :
    PSet.Equiv ((ordinal.mk η).Func i) (ordinal.mk (ordOfMemMk i)) :=
  (Classical.choose_spec
    (equiv_mk_of_mem_mk (η := η) (x := (ordinal.mk η).Func i)
      (mem_mk' (x := ordinal.mk η) (i := i)))).2

theorem mk_injects_into_of_mk_le_omega {η : ordinal}
    (hLe : Cardinal.mk (ordinal.mk η).Type ≤ Cardinal.mk (PSet.omega : pSet.{u}).Type) :
    injects_into (ordinal.mk η) PSet.omega := by
  have hCount : Countable η.ToType := by
    rw [← Ordinal.type_toPSet]
    rw [mk_omega_eq] at hLe
    exact Cardinal.mk_le_aleph0_iff.mp hLe
  let e : η.ToType → Nat := Classical.choose (Countable.exists_injective_nat η.ToType)
  have he : Function.Injective e := Classical.choose_spec (Countable.exists_injective_nat η.ToType)
  let code : (ordinal.mk η).Type → η.ToType :=
    fun i => Ordinal.ToType.mk ⟨ordOfMemMk i, ordOfMemMk_lt i⟩
  refine ⟨pSet.function.mk (fun i => PSet.omega.Func (ULift.up (e (code i)))), ?_⟩
  refine pSet.function.mk_is_injective_function
    (fun i => PSet.omega.Func (ULift.up (e (code i))))
    (fun i => mem_mk' (x := PSet.omega) (i := ULift.up (e (code i))))
    ?_ ?_
  · intro i j hEqv
    have hOrd : ordOfMemMk i = ordOfMemMk j := by
      exact ordinal.mk_inj
        ((func_equiv_ordOfMemMk i).symm.trans (hEqv.trans (func_equiv_ordOfMemMk j)))
    have hCodeIio : Ordinal.ToType.mk.symm (code i) = Ordinal.ToType.mk.symm (code j) := by
      simpa [code] using hOrd
    have hCode : code i = code j := Ordinal.ToType.mk.symm.injective hCodeIio
    have hCodeNat : e (code i) = e (code j) := congrArg e hCode
    simpa [hCodeNat] using
      (PSet.Equiv.rfl :
        PSet.Equiv (PSet.omega.Func (ULift.up (e (code j))))
          (PSet.omega.Func (ULift.up (e (code j)))))
  · intro i₁ i₂ hEqv
    have hCodeULift : ULift.up (e (code i₁)) = ULift.up (e (code i₂)) := omega_inj hEqv
    have hCodeNat : e (code i₁) = e (code i₂) := by
      simpa using hCodeULift
    have hCode : code i₁ = code i₂ := he hCodeNat
    have hOrd : ordOfMemMk i₁ = ordOfMemMk i₂ := by
      simpa [code] using congrArg (fun x : η.ToType => (x : ordinal)) hCode
    exact (func_equiv_ordOfMemMk i₁).trans
      ((mk_equiv_of_eq hOrd).trans (func_equiv_ordOfMemMk i₂).symm)

theorem injects_into_omega_of_mem_aleph_one {z : pSet} (hMem : z ∈ aleph_one) :
    injects_into z PSet.omega := by
  rcases equiv_mk_of_mem_mk hMem with ⟨w, hwlt, hzEq⟩
  have hInj : injects_into (ordinal.mk w) PSet.omega := by
    apply mk_injects_into_of_mk_le_omega
    rw [ordinal.mk_card, mk_omega_eq, Cardinal.card_le_iff]
    rw [aleph_one_eq_succ_aleph_zero] at hwlt
    exact hwlt
  exact (injects_into_congr_left hzEq.symm).1 hInj

theorem aleph_one_satisfies_spec : aleph_one_weak_Ord_spec aleph_one := by
  refine ⟨aleph_one_Ord, ?_⟩
  intro z hz
  rcases hz with ⟨hzOrd, hzNotOmega⟩
  rcases Ord.trichotomy aleph_one_Ord hzOrd with hEq | hLt | hLt
  · exact (PSet.Subset.congr_left hEq).2 subset_refl
  · exact subset_of_mem_Ord hzOrd hLt
  · exact False.elim (hzNotOmega (injects_into_omega_of_mem_aleph_one hLt))

end pSet

end Flypitch
