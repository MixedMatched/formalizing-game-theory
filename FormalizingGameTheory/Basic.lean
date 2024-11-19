import Mathlib.Tactic
import Aesop

-- a Utility is a Rational number representing the payoff for a single player of a given set of strategies
-- (should probably eventually be something with total order and optional decidability)

-- a PureStrategy is an instance of the strategy type
@[aesop safe [constructors, cases]]
structure PureStrategy (A : Type) := (val : A)

def PureStrategy.cast : PureStrategy A → A = M → PureStrategy M
  := by intro PS_A A_eq_M
        subst A_eq_M
        exact PS_A

-- a MixedStrategy is a probability distribution over PureStrategies
@[aesop safe [constructors, cases]]
structure MixedStrategy (A : Type) :=
  (strategies: List (PureStrategy A))
  (probabilities: List Rat)
  (probabilities_sum_to_one: List.foldl (a + b) 0 probabilities = 1)
  (probabilities_non_negative: List.all probabilities (λ p => p > 0))
  (same_length: List.length strategies = List.length probabilities)

-- a Strategy is either a PureStrategy or a MixedStrategy
@[aesop safe [constructors, cases]]
inductive Strategy (A : Type) where
| pure : PureStrategy A → Strategy A
| mixed : MixedStrategy A → Strategy A

@[aesop norm unfold]
def Strategy.isPure : Strategy A → Prop
  | pure _ => True
  | mixed _ => False

@[aesop norm unfold]
def Strategy.intoPure : (s: Strategy A) → s.isPure → PureStrategy A
  | pure p => (λ _ => p)
  | mixed m => by intro a
                  unfold Strategy.isPure at a
                  tauto

def Strategy.downcast : (s: Strategy A) → (ip: s.isPure) → s = Strategy.pure (s.intoPure ip) := by
  intro s ip
  unfold Strategy.intoPure
  unfold Strategy.isPure at ip
  cases s with
  | pure a => simp_all only
  | mixed a_1 =>
    simp_all only [reduceCtorEq]
    tauto

def pure_as_general_eq {p: PureStrategy A} {s: Strategy A} : (ip: s.isPure) → (s.intoPure ip = p) ↔ (s = Strategy.pure p) := by
  intro ip
  constructor
  case mp =>
    intro into
    subst into
    unfold Strategy.intoPure
    unfold Strategy.isPure at ip
    cases s with
    | pure a => simp_all only
    | mixed a_1 =>
      simp_all only [reduceCtorEq]
      simp_all only
  case mpr =>
    intro as_strat
    subst as_strat
    unfold Strategy.intoPure
    unfold Strategy.isPure at ip
    simp_all only

@[aesop safe [constructors, cases]]
structure PureStrategyProfile (L: List Type) where
  (strategies: (i: Fin (List.length L)) → PureStrategy (List.get L i))

-- a StrategyProfile is a list of strategies (for type reasons, we need to use a function)
@[aesop safe [constructors, cases]]
structure StrategyProfile (L: List Type) where
  (strategies: (i: Fin (List.length L)) → Strategy (List.get L i))

@[aesop norm unfold]
def PureStrategyProfile.raiseToStrategyProfile : PureStrategyProfile L → StrategyProfile L :=
  λ psp => ⟨λ i => Strategy.pure (psp.strategies i)⟩

def StrategyProfile.isPure : StrategyProfile L → Prop :=
  λ sp => (∀ (i: Fin L.length), (sp.strategies i).isPure)

@[aesop norm unfold]
def StrategyProfile.lowerToPure : (sp: StrategyProfile L) → sp.isPure → PureStrategyProfile L := by
  intro sp ip
  cases sp
  case mk strategies =>
    apply PureStrategyProfile.mk
    case strategies =>
      intro i
      specialize ip i
      unfold Strategy.isPure at ip
      split at ip
      case h_1 a _ => exact a
      case h_2 _ _ => tauto

-- a UtilityProfile is a list of utilities
@[aesop safe [constructors, cases]]
structure UtilityProfile (L: List Type) where
  (utilities: List Rat)
  (same_length: L.length = utilities.length)

def UtilityProfile.cast : UtilityProfile A → A.length = B.length → UtilityProfile B := by
  intro upa a_eq_b
  exact ⟨upa.utilities, by obtain ⟨utilities, same_length⟩ := upa; simp_all only⟩

instance UtilityProfile.add : Add (UtilityProfile L) where
  add x y := by
    let utilities : List Rat := List.map
      (λ uu => uu.fst + uu.snd)
      (List.zip x.utilities y.utilities)
    let same_length : L.length = utilities.length := by
      unfold utilities
      simp_all only [List.length_map, List.length_zip]
      obtain ⟨utilities_1, same_length_1⟩ := x
      obtain ⟨utilities_2, same_length_2⟩ := y
      simp_all only
      rw [← same_length_1, ← same_length_2]
      simp_all only [min_self]
    let up : UtilityProfile L := ⟨utilities, same_length⟩
    exact up

instance UtilityProfile.mul : HMul Rat (UtilityProfile L) (UtilityProfile L) where
  hMul x y := by
    let utilities : List Rat := List.map
      (λ u => u * x)
      y.utilities
    let same_length : L.length = utilities.length := by
      unfold utilities
      simp_all only [List.length_map]
      obtain ⟨utilities_1, same_length⟩ := y
      simp_all only
    let up : UtilityProfile L := ⟨utilities, same_length⟩
    exact up

def zero_utility_profile (L: List Type) : UtilityProfile L := by
  let utilities : List Rat := List.map (λ _ => 0) L
  let same_length : L.length = utilities.length := by
    simp_all only [List.length_map, utilities]
  let up : UtilityProfile L := ⟨utilities, same_length⟩
  exact up

-- eval_sp automatically converts a pure strategy utility function to a mixed strategy utility function
def eval_sp (S: StrategyProfile L) (PSUF: PureStrategyProfile L → UtilityProfile L) (acc: PureStrategyProfile L) (id: Fin L.length) : UtilityProfile L := by
  by_cases id_not_last :
    id ≥ ⟨
      L.length - 1,
      by simp_all only [tsub_lt_self_iff, zero_lt_one, and_true]
         exact Fin.pos id
    ⟩
  case pos =>
      cases S.strategies id
      case pure p =>
        exact PSUF ⟨by
          intro i
          by_cases id_eq_i : id = i
          case pos =>
              rw [id_eq_i] at p
              exact p
          case neg =>
              exact acc.strategies i
        ⟩
      case mixed m =>
        exact List.foldl
          (λ a b => a + b)
          (by exact zero_utility_profile L)
          (List.map
            (λ a => a.snd *
              (PSUF
                ⟨by
                  intro i
                  by_cases id_eq_i : id = i
                  case pos =>
                      apply Prod.fst at a
                      rw [id_eq_i] at a
                      exact a
                  case neg =>
                      exact acc.strategies i
                ⟩
              )
            )
            (List.zip m.strategies m.probabilities)
          )
  case neg =>
      cases S.strategies id
      case pure p =>
        exact eval_sp S PSUF
          ⟨by
            intro i
            by_cases id_eq_i : id = i
            case pos =>
                rw [id_eq_i] at p
                exact p
            case neg =>
                exact acc.strategies i
          ⟩
          ⟨id.val + 1, by
            simp_all
            conv =>
              equals ↑id < L.length - 1 =>
                simp_all
                apply Iff.intro
                · intro _
                  exact id_not_last
                · intro _
                  exact
                    Nat.add_lt_of_lt_sub
                      id_not_last
            exact id_not_last
          ⟩
      case mixed m =>
        exact List.foldl
          (λ a b => a + b)
          (by exact zero_utility_profile L)
          (List.map
            (λ a => a.snd *
              (eval_sp S PSUF
                ⟨by
                  intro i
                  by_cases id_eq_i : id = i
                  case pos =>
                    apply Prod.fst at a
                    rw [id_eq_i] at a
                    exact a
                  case neg =>
                      exact acc.strategies i
                ⟩
                ⟨id.val + 1, by
                  simp_all
                  conv =>
                    equals ↑id < L.length - 1 =>
                      simp_all
                      apply Iff.intro
                      · intro _
                        exact id_not_last
                      · intro _
                        exact
                          Nat.add_lt_of_lt_sub
                            id_not_last
                  exact id_not_last
                ⟩
              )
            )
            (List.zip m.strategies m.probabilities)
          )
termination_by L.length - id

-- a UtilityFunction is a function that takes a StrategyProfile and returns a Utility
@[aesop safe [constructors, cases]]
inductive UtilityFunction (L: List Type) where
  | mk (x: PureStrategyProfile L → UtilityProfile L) : UtilityFunction L

@[aesop norm unfold]
def UtilityFunction.pure_apply : UtilityFunction L → PureStrategyProfile L → UtilityProfile L
  | mk x => λ p => x p

@[aesop norm unfold]
def UtilityFunction.apply : UtilityFunction L → L.length > 0 → PureStrategyProfile L → StrategyProfile L → UtilityProfile L
  | mk x => λ l psp sp => eval_sp sp x psp ⟨0, l⟩

-- a Game is a number of players, a list of strategies for each player, and a utility function
@[aesop safe [constructors, cases]]
structure Game (L: List Type) where
  (utility: UtilityFunction L)
  (at_least_one_player: List.length L > 0)
  (pure_strategy_profile: PureStrategyProfile L)

def Game.strategy_profile : Game L → StrategyProfile L := by
  intro g
  have psp : PureStrategyProfile L := by exact g.pure_strategy_profile
  let sp : StrategyProfile L := ⟨λ i => Strategy.pure (psp.strategies i)⟩
  exact sp

-- Game.pure_play executes the game for a given PureStrategyProfile, and returns a list of Utilities
def Game.pure_play : Game L → PureStrategyProfile L → UtilityProfile L :=
  λ g psp => g.utility.pure_apply psp

-- Game.play executes the game for a given StrategyProfile, and returns a list of Utilities
@[aesop norm unfold]
def Game.play : Game L → StrategyProfile L → UtilityProfile L :=
  λ g sp => g.utility.apply
              g.at_least_one_player
              (by exact g.pure_strategy_profile)
              sp

-- two strategy profiles are NChange with a list of deltas if those profiles are only possibly
-- different at those deltas
@[aesop norm unfold]
def NChange (L: List Type) (A B: StrategyProfile L) (deltas: List (Fin (List.length L))) : Prop :=
  ∀ (i: Fin (List.length L)), A.strategies i = B.strategies i ∨ deltas.contains i

-- two StrategyProfiles are UnilateralChange if at most one of their players strategies are different
-- (delta is the number of the player whose strategy changed, if one exists)
@[aesop norm unfold]
def UnilateralChange (L: List Type) (A B: StrategyProfile L) (delta: Fin (List.length L)) : Prop :=
  NChange L A B [delta]

-- S does at least as well as S' does at delta
@[aesop norm unfold]
def DoesAtLeastAsWellAs (L: List Type) (G: Game L) (S S': StrategyProfile L) (delta: Fin (List.length L)) : Prop :=
  let thisUtilities: UtilityProfile L := (G.play S)
  let otherUtilities: UtilityProfile L := (G.play S')
  otherUtilities.utilities.get (Fin.cast otherUtilities.same_length delta)
    ≤ thisUtilities.utilities.get (Fin.cast thisUtilities.same_length delta)

-- A StrategyProfile fulfills NashEquilibrium when no player can increase their utility by unilaterally changing their strategy
@[aesop norm unfold]
def NashEquilibrium (L: List Type) (G: Game L) (S: StrategyProfile L) : Prop :=
  -- for every StrategyProfile and delta, if it's a UnilateralChange, S must outperform S' for delta
  ∀ (S': StrategyProfile L)
    (delta: Fin (List.length L)),
    UnilateralChange L S S' delta → DoesAtLeastAsWellAs L G S S' delta

@[simp]
theorem nchange_comm: ∀ (S': StrategyProfile L) (_: NChange L S S' deltas), NChange L S' S deltas := by
  intro S' og
  unfold NChange at og ⊢
  conv => ext i
          pattern S'.strategies i = S.strategies i
          rw [eq_comm]
  exact og

@[simp]
theorem nchange_self: NChange L S S deltas := by
  unfold NChange
  intro i
  left
  rfl

@[simp]
theorem nchange_trans: NChange L S S' deltas1 → NChange L S' S'' deltas2 → NChange L S S'' (deltas1 ++ deltas2) := by
  intro nc1 nc2
  unfold NChange at nc1 nc2 ⊢
  intro i
  specialize nc1 i
  specialize nc2 i
  simp_all only [List.get_eq_getElem, List.elem_eq_mem, decide_eq_true_eq, List.mem_append, Bool.decide_or,
    Bool.or_eq_true]
  cases nc1 with
  | inl h =>
    cases nc2 with
    | inl h_1 => simp_all only [true_or]
    | inr h_2 => simp_all only [or_true]
  | inr h_1 =>
    cases nc2 with
    | inl h => simp_all only [true_or, or_true]
    | inr h_2 => simp_all only [or_self, or_true]

@[simp]
theorem nchange_split: NChange L S S'' (deltas1 ++ deltas2) → ∃ (S': StrategyProfile L), NChange L S S' deltas1 ∧ NChange L S' S'' deltas2 := by
  intro nc
  constructor
  case w =>
    exact ⟨λ x => if deltas2.contains x then S.strategies x else S''.strategies x⟩
  case h =>
    constructor
    case left =>
      intro i
      specialize nc i
      cases nc
      case inl h =>
        simp_all only [List.get_eq_getElem, List.elem_eq_mem, decide_eq_true_eq, ite_self, true_or]
      case inr h =>
        simp_all only [List.elem_eq_mem, List.mem_append, Bool.decide_or, Bool.or_eq_true, decide_eq_true_eq,
          List.get_eq_getElem]
        obtain ⟨strategies⟩ := S
        obtain ⟨strategies_1⟩ := S''
        simp_all only
        cases h with
        | inl h_1 => simp_all only [or_true]
        | inr h_2 => simp_all only [↓reduceIte, true_or]
    case right =>
      intro i
      specialize nc i
      cases nc
      case inl h =>
        simp_all only [List.get_eq_getElem, List.elem_eq_mem, decide_eq_true_eq, ite_self, true_or]
      case inr h =>
        by_cases hdelta : deltas2.contains i
        case pos =>
          simp_all only [List.elem_eq_mem, List.mem_append, Bool.decide_or, Bool.or_eq_true, decide_eq_true_eq,
            List.get_eq_getElem, decide_True, ↓reduceIte, or_true]
        case neg =>
          simp_all only [List.elem_eq_mem, List.mem_append, Bool.decide_or, Bool.or_eq_true, decide_eq_true_eq,
            List.get_eq_getElem, decide_False, Bool.false_eq_true, ↓reduceIte, or_false]

@[simp]
theorem eventually_nchange: ∃ (deltas: List (Fin (List.length L))), NChange L S S' deltas := by
  unfold NChange
  let deltas : List (Fin (List.length L)) := List.finRange (List.length L)
  use deltas
  intro i
  right
  simp_all only [List.elem_eq_mem, List.mem_finRange, decide_True, deltas]

@[simp]
theorem uc_comm: ∀ (S': StrategyProfile L) (_: UnilateralChange L S S' delta), UnilateralChange L S' S delta := by
  intro S' og
  unfold UnilateralChange at og ⊢
  exact nchange_comm S' og

@[simp]
theorem uc_self: UnilateralChange L S S delta := by
  unfold UnilateralChange
  exact nchange_self

@[simp]
theorem uc_trans: UnilateralChange L S S' delta1 → UnilateralChange L S' S'' delta2 → NChange L S S'' [delta1, delta2] := by
  intro uc1 uc2
  unfold UnilateralChange at uc1 uc2
  rw [← List.singleton_append]
  exact nchange_trans uc1 uc2

@[simp]
theorem nchange_to_list_nchange (NC: NChange L S S' deltas):
  (h: (List.length deltas) > 0) →
  ∀ (i: Fin (List.length deltas)),
    ∃ (x x': StrategyProfile L),
      i = ⟨0, by simp_all only [List.get_eq_getElem, List.elem_eq_mem, decide_eq_true_eq, gt_iff_lt]⟩
        → x = S
      ∧ i = ⟨deltas.length - 1, by simp_all only [List.get_eq_getElem, List.elem_eq_mem, decide_eq_true_eq, gt_iff_lt, tsub_lt_self_iff, zero_lt_one, and_self]⟩
        → x' = S'
      ∧ NChange L x x' [deltas[i]]
      := by intro h i
            cases i
            case mk val isLt =>
              induction val
              case zero =>
                use S
                sorry
              sorry

@[simp]
theorem nchange_to_ex_uc (NC: NChange L S S' deltas):
  ∀ (i: Fin (List.length deltas)),
    (h: (List.length deltas) > 0) →
    ∃ (x x': StrategyProfile L),
      i = ⟨0, by simp_all only [List.get_eq_getElem, List.elem_eq_mem, decide_eq_true_eq, gt_iff_lt]⟩
        → x = S
      ∧ i = ⟨deltas.length - 1, by simp_all only [List.get_eq_getElem, List.elem_eq_mem, decide_eq_true_eq, gt_iff_lt, tsub_lt_self_iff, zero_lt_one, and_self]⟩
        → x' = S'
      ∧ UnilateralChange L x x' deltas[i]
      := by exact fun i h ↦ nchange_to_list_nchange NC h i

theorem eventually_uc:
  ∃ (LS: List (StrategyProfile L)),
    (
      LS[0]'(by exact List.length_pos.mpr sorry) = S ∧
      LS[LS.length - 1]'(by simp_all only [ne_eq, tsub_lt_self_iff, zero_lt_one, and_true]
                            exact List.length_pos.mpr sorry) = S' ∧
    ∀ (i: Fin (List.length LS)),
      (hi: i - 1 < LS.length) →
        ∃ (cdelta: Fin (List.length L)),
        UnilateralChange L (LS.get ⟨i.val - 1, by simp_all only [ne_eq]⟩) (LS.get i) cdelta)
      := by sorry

@[simp]
theorem dalawa_inv: ¬DoesAtLeastAsWellAs L G S S' delta → DoesAtLeastAsWellAs L G S' S delta := by
  intro not_dalawa
  unfold DoesAtLeastAsWellAs at not_dalawa ⊢
  simp_all only [List.get_eq_getElem, Fin.coe_cast, not_le]
  exact le_of_lt not_dalawa

@[simp]
theorem dalawa_self: DoesAtLeastAsWellAs L G S S delta := by
  unfold DoesAtLeastAsWellAs
  simp_all only [List.get_eq_getElem, Fin.coe_cast, le_refl]

theorem dalawa_trans: DoesAtLeastAsWellAs L G S S' delta → DoesAtLeastAsWellAs L G S' S'' delta → DoesAtLeastAsWellAs L G S S'' delta := by
  unfold DoesAtLeastAsWellAs
  intro ss' s's''
  unfold Game.play at ss' s's'' ⊢
  unfold UtilityFunction.apply at ss' s's'' ⊢
  simp_all only [List.get_eq_getElem, Fin.coe_cast]
  sorry
  /- exact
    Preorder.le_trans
      (eval_sp S'' G.1.1 G.pure_strategy_profile ⟨0, PlayGame.proof_1 L N G⟩).utilities[↑delta]
      (eval_sp S' G.1.1 G.pure_strategy_profile ⟨0, PlayGame.proof_1 L N G⟩).utilities[↑delta]
      (eval_sp S G.1.1 G.pure_strategy_profile ⟨0, PlayGame.proof_1 L N G⟩).utilities[↑delta]
      s's''
      ss' -/

@[simp]
theorem nasheq_exists: NashEquilibrium L G S
  := by sorry -- we need to use a fixed point theorem here :p

@[simp]
theorem not_nasheq_if_uc_better: UnilateralChange L A B i ∧ ¬DoesAtLeastAsWellAs L G B A i → ¬NashEquilibrium L G B := by
  intro h ne
  unfold NashEquilibrium at ne
  have uc: UnilateralChange L B A i := by apply And.left at h
                                          apply uc_comm at h
                                          exact h
  apply ne at uc
  let au: UtilityProfile L := (G.play A)
  let bu: UtilityProfile L := (G.play B)
  have greater: au.utilities.get (Fin.cast au.same_length i) > bu.utilities.get (Fin.cast bu.same_length i)
    := by apply And.right at h
          unfold DoesAtLeastAsWellAs at h
          simp_all only [List.get_eq_getElem, Fin.coe_cast, not_le, gt_iff_lt]
  apply not_le_of_gt at greater
  tauto

@[simp]
theorem exists_better_uc_if_not_nasheq:
    ¬NashEquilibrium L G S
      → (∃ (S': StrategyProfile L) (delta: Fin (List.length L)),
          UnilateralChange L S S' delta ∧ DoesAtLeastAsWellAs L G S' S delta) := by
  intro not_ne
  unfold NashEquilibrium at not_ne
  simp_all
  obtain ⟨S', h⟩ := not_ne
  obtain ⟨delta, h⟩ := h
  obtain ⟨left, right⟩ := h
  apply dalawa_inv at right
  use S'
  use delta

@[simp]
theorem better_than_all_ucs_is_nasheq:
    (∀ (S': StrategyProfile L) (delta: Fin (List.length L)),
      UnilateralChange L S S' delta → DoesAtLeastAsWellAs L G S S' delta)
        → NashEquilibrium L G S := by
  intro as'delta
  unfold NashEquilibrium
  intro S' delta uc
  apply as'delta at uc
  exact uc

@[simp]
theorem all_ucs_not_nash_eq_then_nash_eq: (∀ (S': StrategyProfile L) (delta: Fin (List.length L)), UnilateralChange L S S' delta → ¬NashEquilibrium L G S') → NashEquilibrium L G S := by
  have Sne : StrategyProfile L := G.strategy_profile
  have nes' : NashEquilibrium L G Sne
    := by exact nasheq_exists
  intro as'delta S' delta uc
  by_cases S_is_ne : Sne = S
  case pos =>
    subst S_is_ne
    apply nes'
    exact uc
  case neg =>
    by_cases ne_is_uc : UnilateralChange L S Sne delta
    case pos =>
      specialize as'delta Sne delta ne_is_uc
      tauto
    case neg =>
      sorry

-- Example: Prisoner's Dilemma
-- Two prisoners are arrested for a crime. They are held in separate cells and cannot communicate with each other.
-- The prosecutor lacks sufficient evidence to convict the pair on the principal charge, but he has enough to convict both on a lesser charge.
-- Simultaneously, the prosecutor offers each prisoner a bargain. Each prisoner is given the opportunity either to betray the other by
-- testifying that the other committed the crime, or to cooperate with the other by remaining silent.

-- The offer is as follows, where the numbers in parentheses represent the utility, the inverse of the sentence in years:
-- +----------+---------+----------+---------+
-- |          |         | Player 2 |         |
-- +----------+---------+----------+---------+
-- |          |         | Silent   | Confess |
-- | Player 1 | Silent  | 3, 3     | 1, 4    |
-- |          | Confess | 4, 1     | 2, 2    |
-- +----------+---------+----------+---------+

@[aesop safe [constructors, cases]]
inductive PrisonersDilemmaStrategies where
| silent
| confess

@[aesop norm unfold]
def PL : List Type := [PrisonersDilemmaStrategies, PrisonersDilemmaStrategies]

def PL_length : List.length PL = 2 := rfl

@[aesop norm unfold]
def PrisonersDilemmaUtilityFunction : UtilityFunction PL :=
  ⟨λ S => match (S.strategies (Fin.ofNat 0)).val, (S.strategies (Fin.ofNat 1)).val with
          | PrisonersDilemmaStrategies.silent,  PrisonersDilemmaStrategies.silent  => { utilities := [3, 3], same_length := rfl }
          | PrisonersDilemmaStrategies.silent,  PrisonersDilemmaStrategies.confess => { utilities := [1, 4], same_length := rfl }
          | PrisonersDilemmaStrategies.confess, PrisonersDilemmaStrategies.silent  => { utilities := [4, 1], same_length := rfl }
          | PrisonersDilemmaStrategies.confess, PrisonersDilemmaStrategies.confess => { utilities := [2, 2], same_length := rfl }
  ⟩

@[aesop norm unfold]
def PrisonersDilemmaPureProfile : PureStrategyProfile PL :=
  { strategies := λ i => match i with
                          | ⟨0, _⟩ => ⟨PrisonersDilemmaStrategies.silent⟩
                          | ⟨1, _⟩ => ⟨PrisonersDilemmaStrategies.silent⟩
  }

@[aesop norm unfold]
def PrisonersDilemmaSilentSilentProfile : StrategyProfile PL :=
  { strategies := λ i => match i with
                          | ⟨0, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.silent⟩
                          | ⟨1, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.silent⟩
  }

@[aesop norm unfold]
def PrisonersDilemmaSilentConfessProfile : StrategyProfile PL :=
  { strategies := λ i => match i with
                          | ⟨0, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.silent⟩
                          | ⟨1, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.confess⟩
  }

@[aesop norm unfold]
def PrisonersDilemmaConfessConfessProfile : StrategyProfile PL :=
  { strategies := λ i => match i with
                          | ⟨0, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.confess⟩
                          | ⟨1, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.confess⟩
  }

@[aesop norm unfold]
def PrisonersDilemmaGame : Game PL :=
{ utility := PrisonersDilemmaUtilityFunction,
  at_least_one_player := Nat.zero_lt_succ 1
  pure_strategy_profile := by exact PrisonersDilemmaPureProfile
}

theorem PDSilentConfessIsUnilateralOfPDSilentSilent : UnilateralChange PL PrisonersDilemmaSilentConfessProfile PrisonersDilemmaSilentSilentProfile (Fin.mk 1 x) := by
  unfold UnilateralChange
  intro i
  cases i
  case mk val isLt =>
    cases val
    case zero =>  left
                  unfold PrisonersDilemmaSilentSilentProfile
                  unfold PrisonersDilemmaSilentConfessProfile
                  simp_all
    case succ n =>
      cases n
      case zero =>  right
                    simp_all
      case succ m =>  rw [PL_length] at isLt
                      conv at isLt => lhs
                                      change m + 2
                                      rw [add_comm]
                      simp only [add_lt_iff_neg_left, not_lt_zero'] at isLt

theorem NotNashEquilibriumSilentSilent : ¬ NashEquilibrium PL PrisonersDilemmaGame PrisonersDilemmaSilentSilentProfile := by
  apply not_nasheq_if_uc_better
  case i =>
    rw [PL_length]
    exact Fin.last 1
  case a =>
    constructor
    case left => exact PDSilentConfessIsUnilateralOfPDSilentSilent
    case right => unfold PL PrisonersDilemmaGame PrisonersDilemmaSilentSilentProfile
                    PrisonersDilemmaSilentConfessProfile PrisonersDilemmaPureProfile PrisonersDilemmaUtilityFunction
                    DoesAtLeastAsWellAs Game.play UtilityFunction.apply eval_sp
                  simp_all [↓dreduceDIte]
                  unfold eval_sp
                  simp_all [↓reduceDIte]
                  rfl

theorem ConfessConfessDALAWAMixedOne :
    ∀ m: MixedStrategy PrisonersDilemmaStrategies,
      DoesAtLeastAsWellAs PL PrisonersDilemmaGame
        PrisonersDilemmaConfessConfessProfile
        ⟨λ i => match i with
                | ⟨0, _⟩ => Strategy.mixed m
                | ⟨1, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.confess⟩⟩
        ⟨0, by unfold PL; simp_all⟩
        := by
  intro m
  unfold DoesAtLeastAsWellAs
  intro thisUtilities otherUtilities
  unfold thisUtilities otherUtilities Game.play PrisonersDilemmaGame PrisonersDilemmaUtilityFunction PrisonersDilemmaConfessConfessProfile
  unfold PL at thisUtilities
  unfold PL at otherUtilities
  unfold UtilityFunction.apply
  simp_all only [List.length_singleton, List.get_eq_getElem, Fin.zero_eta, Fin.isValue, Fin.val_zero, Fin.mk_one,
    Fin.val_one, Fin.cast_zero]
  sorry

theorem NashEquilibriumConfessConfess : NashEquilibrium PL PrisonersDilemmaGame PrisonersDilemmaConfessConfessProfile := by
  apply better_than_all_ucs_is_nasheq
  unfold PL PrisonersDilemmaGame PrisonersDilemmaPureProfile PrisonersDilemmaUtilityFunction PrisonersDilemmaConfessConfessProfile
    DoesAtLeastAsWellAs Game.play UtilityFunction.apply eval_sp
  intro sp delta uc
  intro thisUtilities otherUtilities
  unfold UnilateralChange at uc
  unfold NChange at uc
  simp_all [↓dreduceDIte, otherUtilities, thisUtilities]
  obtain ⟨strategies⟩ := sp
  simp_all only [Fin.isValue]
  sorry

-- Example: Rock-Paper-Scissors

inductive RockPaperScissorsStrategies where
| rock
| paper
| scissors

def RPS : List Type := [RockPaperScissorsStrategies, RockPaperScissorsStrategies]
def RPS_length : List.length RPS = 2 := rfl

def RockPaperScissorsUtilityFunction : UtilityFunction RPS :=
  ⟨λ S => match (S.strategies (Fin.ofNat 0)).val, (S.strategies (Fin.ofNat 1)).val with
          | RockPaperScissorsStrategies.rock,     RockPaperScissorsStrategies.rock     => { utilities := [1, 1], same_length := rfl }
          | RockPaperScissorsStrategies.rock,     RockPaperScissorsStrategies.paper    => { utilities := [0, 2], same_length := rfl }
          | RockPaperScissorsStrategies.rock,     RockPaperScissorsStrategies.scissors => { utilities := [2, 0], same_length := rfl }
          | RockPaperScissorsStrategies.paper,    RockPaperScissorsStrategies.rock     => { utilities := [2, 0], same_length := rfl }
          | RockPaperScissorsStrategies.paper,    RockPaperScissorsStrategies.paper    => { utilities := [1, 1], same_length := rfl }
          | RockPaperScissorsStrategies.paper,    RockPaperScissorsStrategies.scissors => { utilities := [0, 2], same_length := rfl }
          | RockPaperScissorsStrategies.scissors, RockPaperScissorsStrategies.rock     => { utilities := [0, 2], same_length := rfl }
          | RockPaperScissorsStrategies.scissors, RockPaperScissorsStrategies.paper    => { utilities := [2, 0], same_length := rfl }
          | RockPaperScissorsStrategies.scissors, RockPaperScissorsStrategies.scissors => { utilities := [1, 1], same_length := rfl }
  ⟩

def RPSPureProfile : PureStrategyProfile RPS :=
  { strategies := λ i => match i with
                          | ⟨0, _⟩ => ⟨RockPaperScissorsStrategies.paper⟩
                          | ⟨1, _⟩ => ⟨RockPaperScissorsStrategies.scissors⟩
  }

def RockPaperScissorsGame : Game RPS :=
  { utility := RockPaperScissorsUtilityFunction,
    at_least_one_player := Nat.zero_lt_succ 1
    pure_strategy_profile := by exact RPSPureProfile
  }

-- Example: Nash Demand Game

-- Two players are asked to demand a share of some good. If the sum of the demands is less than or equal to the total amount available,
-- then both players get their demand. Otherwise, neither player gets anything.

structure NashDemandChoice where
  (demand: Rat)
  (demand_nonnegative: demand ≥ 0)
  (demand_le_one: demand ≤ 1)

def NashDemandChoiceList : List Type := [NashDemandChoice, NashDemandChoice]

def NashDemandUtilityFunction : UtilityFunction NashDemandChoiceList :=
  ⟨λ S => match S.strategies (Fin.ofNat 0), S.strategies (Fin.ofNat 1) with
          | ⟨d1, _, _⟩, ⟨d2, _, _⟩ =>
            let d12 : Rat := d1 + d2
            let oneUtility : Rat := 1
              if d12 ≤ oneUtility then { utilities := [d1, d2], same_length := rfl }
            else { utilities := [0, 0], same_length := rfl }
  ⟩

def NDC_Pure : PureStrategyProfile NashDemandChoiceList :=
  { strategies := λ i => match i with
                          | ⟨0, _⟩ => ⟨
                            ⟨1, by exact rfl, by exact Preorder.le_refl 1 ⟩
                          ⟩
                          | ⟨1, _⟩ => ⟨
                            ⟨1, by exact rfl, by exact Preorder.le_refl 1 ⟩
                          ⟩
  }

def NashDemandGame : Game NashDemandChoiceList :=
  { utility := NashDemandUtilityFunction,
    at_least_one_player := Nat.zero_lt_succ 1
    pure_strategy_profile := by exact NDC_Pure
  }

-- Example: Iterated Prisoner's Dilemma for 5 rounds

structure IPD_Strategy where
  (strategy_function: List PrisonersDilemmaStrategies → PrisonersDilemmaStrategies)

def IPDList : List Type := [IPD_Strategy, IPD_Strategy]

def IPD_UtilityRecurse (psp: PureStrategyProfile IPDList) (p1_list: List PrisonersDilemmaStrategies) (p2_list: List PrisonersDilemmaStrategies) (iter: Nat) : UtilityProfile IPDList := by
  by_cases iter = 0
  case pos => exact zero_utility_profile IPDList
  case neg =>
    let p1_choice : PrisonersDilemmaStrategies := (psp.strategies (Fin.ofNat 0)).val.strategy_function p1_list
    let p2_choice : PrisonersDilemmaStrategies := (psp.strategies (Fin.ofNat 1)).val.strategy_function p2_list
    let current_round_utilities :=
      PrisonersDilemmaUtilityFunction.pure_apply
        ⟨λ i => match i with
                | ⟨0, _⟩ => PureStrategy.mk p1_choice
                | ⟨1, _⟩ => PureStrategy.mk p2_choice⟩
    have PL_eq_IPDLLength : PL.length = IPDList.length := by unfold PL
                                                             unfold PL at current_round_utilities
                                                             simp_all
                                                             rfl
    let current_round_utilities_casted := current_round_utilities.cast PL_eq_IPDLLength
    exact current_round_utilities_casted
      + (IPD_UtilityRecurse psp (p1_choice::p1_list) (p2_choice::p2_list) (iter - 1))

def IPD_UtilityFunction : UtilityFunction IPDList :=
  ⟨λ S => IPD_UtilityRecurse S [] [] 5⟩

def AlwaysConfess : PureStrategyProfile IPDList :=
  { strategies := λ i => match i with
                          | ⟨0, _⟩ => ⟨⟨λ _ => PrisonersDilemmaStrategies.confess⟩⟩
                          | ⟨1, _⟩ => ⟨⟨λ _ => PrisonersDilemmaStrategies.confess⟩⟩
  }

def IPDGame : Game IPDList :=
  { utility := IPD_UtilityFunction
    at_least_one_player := Nat.zero_lt_succ 1
    pure_strategy_profile := by exact AlwaysConfess
  }
