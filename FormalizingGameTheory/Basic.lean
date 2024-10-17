import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Aesop
import Paperproof

-- a Utility is a Real number representing the payoff of a given set of strategies

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

@[aesop safe [constructors, cases]]
structure PureStrategyProfile (L: List Type) where
  (strategies: (i: Fin (List.length L)) → PureStrategy (List.get L i))

-- a StrategyProfile is a list of strategies (for type reasons, we need to use a function)
@[aesop safe [constructors, cases]]
structure StrategyProfile (L: List Type) where
  (strategies: (i: Fin (List.length L)) → Strategy (List.get L i))

-- a UtilityProfile is a list of utilities
@[aesop safe [constructors, cases]]
structure UtilityProfile (L: List Type) where
  (utilities: List Rat)
  (same_length: L.length = utilities.length)

instance UtilityProfile.add : Add (UtilityProfile L) where
  add x y := by let utilities : List Rat := List.map (λ uu => uu.fst + uu.snd) (List.zip x.utilities y.utilities)
                let same_length : L.length = utilities.length := by unfold utilities
                                                                    simp_all only [List.length_map, List.length_zip]
                                                                    obtain ⟨utilities_1, same_length_1⟩ := x
                                                                    obtain ⟨utilities_2, same_length_2⟩ := y
                                                                    simp_all only
                                                                    rw [← same_length_1, ← same_length_2]
                                                                    simp_all only [min_self]
                let up : UtilityProfile L := ⟨utilities, same_length⟩
                exact up

instance UtilityProfile.mul : HMul Rat (UtilityProfile L) (UtilityProfile L) where
  hMul x y := by let utilities : List Rat := List.map (λ u => u * x) y.utilities
                 let same_length : L.length = utilities.length := by unfold utilities
                                                                     simp_all only [List.length_map]
                                                                     obtain ⟨utilities_1, same_length⟩ := y
                                                                     simp_all only
                 let up : UtilityProfile L := ⟨utilities, same_length⟩
                 exact up

def zero_utility_profile (L: List Type) : UtilityProfile L
  := by let utilities : List Rat := List.map (λ _ => 0) L
        let same_length : L.length = utilities.length := by simp_all only [List.length_map, utilities]
        let up : UtilityProfile L := ⟨utilities, same_length⟩
        exact up

-- eval_sp automatically converts a pure strategy utility function to a mixed strategy utility function
def eval_sp (S: StrategyProfile L) (PSUF: PureStrategyProfile L → UtilityProfile L) (acc: PureStrategyProfile L) (id: Fin L.length) : UtilityProfile L
  := by by_cases id_not_last : id ≥ ⟨L.length - 1, by simp_all only [tsub_lt_self_iff, zero_lt_one, and_true]
                                                      exact Fin.pos id
                                    ⟩
        case pos =>
            cases S.strategies id
            case pure p => exact PSUF ⟨
                                 by intro i
                                    by_cases id_eq_i : id = i
                                    case pos =>
                                        rw [id_eq_i] at p
                                        exact p
                                    case neg =>
                                        exact acc.strategies i
                               ⟩
            case mixed m => exact List.foldl (λ a b => a + b)
                                      (by exact zero_utility_profile L)
                                      (List.map (λ a => a.snd * (PSUF ⟨
                                                   by intro i
                                                      by_cases id_eq_i : id = i
                                                      case pos =>
                                                          apply Prod.fst at a
                                                          rw [id_eq_i] at a
                                                          exact a
                                                      case neg =>
                                                          exact acc.strategies i
                                                ⟩))
                                                (List.zip m.strategies m.probabilities))
        case neg =>
            cases S.strategies id
            case pure p => exact eval_sp S PSUF ⟨
                                 by intro i
                                    by_cases id_eq_i : id = i
                                    case pos =>
                                        rw [id_eq_i] at p
                                        exact p
                                    case neg =>
                                        exact acc.strategies i
                               ⟩ ⟨id.val + 1, by simp_all
                                                 conv => equals ↑id < L.length - 1 => simp_all
                                                                                      apply Iff.intro
                                                                                      · intro _
                                                                                        exact id_not_last
                                                                                      · intro _
                                                                                        exact
                                                                                          Nat.add_lt_of_lt_sub
                                                                                            id_not_last
                                                 exact id_not_last
                                 ⟩
            case mixed m => exact List.foldl (λ a b => a + b)
                                      (by exact zero_utility_profile L)
                                      (List.map (λ a => a.snd * (eval_sp S PSUF ⟨
                                                   by intro i
                                                      by_cases id_eq_i : id = i
                                                      case pos =>
                                                          apply Prod.fst at a
                                                          rw [id_eq_i] at a
                                                          exact a
                                                      case neg =>
                                                          exact acc.strategies i
                                                ⟩ ⟨id.val + 1, by simp_all
                                                                  conv => equals ↑id < L.length - 1 =>  simp_all
                                                                                                        apply Iff.intro
                                                                                                        · intro _
                                                                                                          exact id_not_last
                                                                                                        · intro _
                                                                                                          exact
                                                                                                            Nat.add_lt_of_lt_sub
                                                                                                              id_not_last
                                                                  exact id_not_last
                                                  ⟩))
                                                (List.zip m.strategies m.probabilities))
termination_by L.length - id

-- a UtilityFunction is a function that takes a StrategyProfile and returns a Utility
@[aesop safe [constructors, cases]]
inductive UtilityFunction (L: List Type) where
  | mk (x: PureStrategyProfile L → UtilityProfile L) : UtilityFunction L

def UtilityFunction.pure_apply : UtilityFunction L → PureStrategyProfile L → UtilityProfile L
  | mk x => λ p => x p

@[aesop norm unfold]
def UtilityFunction.apply : UtilityFunction L → L.length > 0 → PureStrategyProfile L → StrategyProfile L → UtilityProfile L
  | mk x => λ l psp sp => eval_sp sp x psp ⟨0, l⟩

-- a Game is a number of players, a list of strategies for each player, and a utility function
@[aesop safe [constructors, cases]]
structure Game (L: List Type) (N: Nat) where
  (utility: UtilityFunction L)
  (same_length: (List.length L) = N)
  (at_least_one_player: N > 0)
  (pure_strategy_profile: PureStrategyProfile L)

def Game.strategy_profile : Game L N → StrategyProfile L
  := by intro g
        have psp : PureStrategyProfile L := by exact g.pure_strategy_profile
        let sp : StrategyProfile L := ⟨λ i => Strategy.pure (psp.strategies i)⟩
        exact sp

def PlayPureGame (L: List Type) (N: Nat) (G: Game L N) (PS: PureStrategyProfile L) : UtilityProfile L := G.utility.pure_apply PS

-- a PlayGame is a function that takes a Game, a StrategyProfile, and returns a list of Utilities
@[aesop norm unfold]
def PlayGame (L: List Type) (N: Nat) (G: Game L N) (S: StrategyProfile L) : UtilityProfile L
  := G.utility.apply
      (by simp_all only [gt_iff_lt]
          obtain ⟨_, same_length, at_least_one_player, _⟩ := G
          subst same_length
          simp_all only [gt_iff_lt])
      (by exact G.pure_strategy_profile)
      S

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
def DoesAtLeastAsWellAs (L: List Type) (N: Nat) (G: Game L N) (S S': StrategyProfile L) (delta: Fin (List.length L)) : Prop :=
  let thisUtilities: UtilityProfile L := (PlayGame L N G S)
  let otherUtilities: UtilityProfile L := (PlayGame L N G S')
  otherUtilities.utilities.get (Fin.cast otherUtilities.same_length delta) ≤ thisUtilities.utilities.get (Fin.cast thisUtilities.same_length delta)

-- A StrategyProfile fulfills NashEquilibrium when no player can increase their utility by unilaterally changing their strategy
@[aesop norm unfold]
def NashEquilibrium (L: List Type) (N: Nat) (G: Game L N) (S: StrategyProfile L) : Prop :=
  -- for every StrategyProfile and delta, if it's a UnilateralChange, S must outperform S' for delta
  ∀ (S': StrategyProfile L)
    (delta: Fin (List.length L)),
    UnilateralChange L S S' delta → DoesAtLeastAsWellAs L N G S S' delta

@[simp]
theorem nchange_comm:
  ∀ (S': StrategyProfile L)
    (_: NChange L S S' deltas),
    NChange L S' S deltas
    := by intro S' og
          unfold NChange at og ⊢
          conv => ext i
                  pattern S'.strategies i = S.strategies i
                  rw [eq_comm]
          exact og

@[simp]
theorem nchange_self:
  NChange L S S deltas
  := by unfold NChange
        intro i
        left
        rfl

@[simp]
theorem nchange_trans:
  NChange L S S' deltas1 → NChange L S' S'' deltas2 → NChange L S S'' (deltas1 ++ deltas2)
  := by intro nc1 nc2
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
theorem nchange_split:
  NChange L S S'' (deltas1 ++ deltas2) → ∃ (S': StrategyProfile L), NChange L S S' deltas1 ∧ NChange L S' S'' deltas2
  := by intro nc
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
theorem eventually_nchange:
  ∃ (deltas: List (Fin (List.length L))),
    NChange L S S' deltas
    := by unfold NChange
          let deltas : List (Fin (List.length L)) := List.finRange (List.length L)
          use deltas
          intro i
          right
          simp_all only [List.elem_eq_mem, List.mem_finRange, decide_True, deltas]

@[simp]
theorem uc_comm:
  ∀ (S': StrategyProfile L)
    (_: UnilateralChange L S S' delta),
    UnilateralChange L S' S delta
    := by intro S' og
          unfold UnilateralChange at og ⊢
          exact nchange_comm S' og

@[simp]
theorem uc_self:
  UnilateralChange L S S delta
  := by unfold UnilateralChange
        exact nchange_self

@[simp]
theorem uc_trans:
  UnilateralChange L S S' delta1 → UnilateralChange L S' S'' delta2 → NChange L S S'' [delta1, delta2]
  := by intro uc1 uc2
        unfold UnilateralChange at uc1 uc2
        rw [← List.singleton_append]
        exact nchange_trans uc1 uc2

@[simp]
theorem nchange_to_list_nchange (NC: NChange L S S' deltas):
  ∀ (i: Fin (List.length deltas)),
    ∃ (x x': StrategyProfile L),
      NChange L x x' [deltas[i]]
      := by intro i
            simp_all only [List.get_eq_getElem, List.elem_eq_mem, decide_eq_true_eq, Fin.getElem_fin, List.mem_singleton]
            obtain ⟨strategies⟩ := S
            apply Exists.intro
            · apply Exists.intro
              · intro i_1
                apply Or.inl
                rfl
              · apply StrategyProfile.mk
                intro i_1
                simp_all only [List.get_eq_getElem]
                apply strategies

@[simp]
theorem nchange_to_list_uc (NC: NChange L S S' deltas):
  ∀ (i: Fin (List.length deltas)),
    ∃ (x x': StrategyProfile L),
      UnilateralChange L x x' deltas[i]
      := by exact fun i ↦ nchange_to_list_nchange NC i

theorem eventually_uc:
  ∃ (LS: List (StrategyProfile L)),
    LS ≠ [] ∧ LS[0]'sorry = S ∧ LS[LS.length - 1]'sorry = S' ∧
    ∀ (i: Fin (List.length LS)),
      i > ⟨0, sorry⟩ →
        ∃ (cdelta: Fin (List.length L)),
        UnilateralChange L (LS.get (i - ⟨1, sorry⟩)) (LS.get i) cdelta
      := by sorry

@[simp]
theorem dalawa_inv:
  ∀ (S': StrategyProfile L),
    ¬DoesAtLeastAsWellAs L N G S S' delta → DoesAtLeastAsWellAs L N G S' S delta
    := by intro S' not_dalawa
          unfold DoesAtLeastAsWellAs at not_dalawa ⊢
          simp_all only [List.get_eq_getElem, Fin.coe_cast, not_le]
          exact le_of_lt not_dalawa

@[simp]
theorem dalawa_self:
  DoesAtLeastAsWellAs L N G S S delta
    := by unfold DoesAtLeastAsWellAs
          simp_all

@[simp]
theorem nasheq_exists:
  ∃ (S: StrategyProfile L), NashEquilibrium L N G S
  := by cases N
        case zero => have impossible : 0 > 0 := by exact (Game.at_least_one_player G)
                     tauto
        case succ n =>
          have S : StrategyProfile L := by exact G.strategy_profile
          by_cases h : ∃ (x: StrategyProfile L), x ≠ S
          case neg =>
            simp_all
            use S
            unfold NashEquilibrium
            intro S' delta uc
            specialize h S'
            rw[h]
            exact dalawa_self
          case pos =>
            simp_all
            obtain ⟨S', neq⟩ := h
            sorry -- we need to use a fixed point theorem here :p

@[simp]
theorem not_nasheq_if_uc_better:
  UnilateralChange L A B i ∧ ¬DoesAtLeastAsWellAs L N G B A i → ¬NashEquilibrium L N G B
  := by intro h ne
        unfold NashEquilibrium at ne
        have uc: UnilateralChange L B A i := by apply And.left at h
                                                apply uc_comm at h
                                                exact h
        apply ne at uc
        let au: UtilityProfile L := (PlayGame L N G A)
        let bu: UtilityProfile L := (PlayGame L N G B)
        have greater: au.utilities.get (Fin.cast au.same_length i) > bu.utilities.get (Fin.cast bu.same_length i)
          := by apply And.right at h
                unfold DoesAtLeastAsWellAs at h
                simp_all only [List.get_eq_getElem, Fin.coe_cast, not_le, gt_iff_lt]
        apply not_le_of_gt at greater
        tauto

@[simp]
theorem exists_better_uc_if_not_nasheq:
  ¬NashEquilibrium L N G S → (∃ (S': StrategyProfile L) (delta: Fin (List.length L)), UnilateralChange L S S' delta ∧ DoesAtLeastAsWellAs L N G S' S delta)
  := by intro not_ne
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
    UnilateralChange L S S' delta → DoesAtLeastAsWellAs L N G S S' delta) → NashEquilibrium L N G S
    := by intro as'delta
          unfold NashEquilibrium
          intro S' delta uc
          apply as'delta at uc
          exact uc

@[simp]
theorem all_ucs_not_nash_eq_then_nash_eq:
  (∀ (S': StrategyProfile L) (delta: Fin (List.length L)),
    UnilateralChange L S S' delta → ¬NashEquilibrium L N G S') → NashEquilibrium L N G S
    := by have ene : ∃ (Sne: StrategyProfile L), NashEquilibrium L N G Sne
            := by exact nasheq_exists
          obtain ⟨Sne, nes'⟩ := ene
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
def PrisonersDilemmaGame : Game PL 2 :=
{ utility := PrisonersDilemmaUtilityFunction,
  same_length := rfl,
  at_least_one_player := Nat.zero_lt_succ 1
  pure_strategy_profile := by exact PrisonersDilemmaPureProfile
}

theorem PDSilentConfessIsUnilateralOfPDSilentSilent : UnilateralChange PL PrisonersDilemmaSilentConfessProfile PrisonersDilemmaSilentSilentProfile (Fin.mk 1 x)
  := by unfold UnilateralChange
        intro i
        cases i
        case mk val isLt =>
          cases val
          case zero => left
                       unfold PrisonersDilemmaSilentSilentProfile
                       unfold PrisonersDilemmaSilentConfessProfile
                       simp_all
          case succ n =>
            cases n
            case zero => right
                         simp_all
            case succ m => rw [PL_length] at isLt
                           conv at isLt => lhs
                                           change m + 2
                                           rw [add_comm]
                           simp_all only [add_zero, add_lt_iff_neg_left, not_lt_zero']

theorem NotNashEquilibriumSilentSilent : ¬ NashEquilibrium PL 2 PrisonersDilemmaGame PrisonersDilemmaSilentSilentProfile
  := by apply not_nasheq_if_uc_better
        case i =>
          rw [PL_length]
          exact Fin.last 1
        case a =>
          constructor
          case left => exact PDSilentConfessIsUnilateralOfPDSilentSilent
          case right => unfold PL PrisonersDilemmaGame PrisonersDilemmaSilentSilentProfile
                          PrisonersDilemmaSilentConfessProfile PrisonersDilemmaPureProfile PrisonersDilemmaUtilityFunction
                          DoesAtLeastAsWellAs PlayGame UtilityFunction.apply eval_sp
                        simp_all [↓dreduceDIte]
                        unfold eval_sp
                        simp_all [↓reduceDIte]
                        rfl

theorem NashEquilibriumConfessConfess : NashEquilibrium PL 2 PrisonersDilemmaGame PrisonersDilemmaConfessConfessProfile
  := by sorry

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

def RockPaperScissorsGame : Game RPS 2 :=
  { utility := RockPaperScissorsUtilityFunction,
    same_length := rfl,
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

def NashDemandGame : Game NashDemandChoiceList 2 :=
  { utility := NashDemandUtilityFunction,
    same_length := rfl,
    at_least_one_player := Nat.zero_lt_succ 1
    pure_strategy_profile := by exact NDC_Pure
  }
