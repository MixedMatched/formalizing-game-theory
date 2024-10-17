# Formalizing Game Theory in Lean

Formalizing Game Theory in the Lean proof language holds significant promise for advancing both the theoretical foundations and practical applications of game-theoretic models. Lean, known for its precision and rigor in formal verification, offers a robust framework for expressing and proving mathematical theorems. By formalizing Game Theory in Lean, researchers and practitioners can establish a rigorous basis for analyzing strategic interactions, ensuring the correctness of game-theoretic concepts, and facilitating automated verification of complex game structures. 

This repository contains an example of formal structures and properties to represent and reason about games in Lean. While there have been other attempts to make such a formalization, the representation proposed here is novel in that it can represent a much broader class of games than previous attempts. In particular, this formalization is able to represent games with more than 2 players, games with a continuous set of actions, and games with intricate utility functions.

The relevant code for this repository can be found [here](https://github.com/MixedMatched/formalizing-game-theory/blob/master/FormalizingGameTheory/Basic.lean).

## Formalization

Our formalization starts with a definition of Utility as equivalent to Mathlib.Data.Rat. While many different types could be used to represent preference order, we chose to restrict the formalization to rational numbers because they still have the properties of total order and continuity, while also being easy to work with in Lean (comparisons between the rationals are decidable, while comparisons between the reals are not).

We then represent a Pure Strategy as:

```lean
structure PureStrategy (A : Type) := (val : A)
```

which defines a Pure Strategy as an instance of some type `A`. This means that a player's available strategies are defined with a type `A`, and an individual strategy is defined as an instance of that type. For example, in the game of Stag Hunt, the avalable strategies could be formalized as the type:

```lean
inductive StagHuntStrategies
| stag
| hare
```

and a strategy for player 1 could be formalized as the instance `PureStrategy StagHuntStrategies.stag`. This representation allows for a wide variety of games to be formalized, including games with a continuous set of actions. For example, the Nash Demand Game could be formalized with the type:

```lean
structure NashDemandStrategies :=
    (demand : Rat)
    (above_0: demand > 0)
    (below_1: demand < 1)
```

and a strategy for player 1 could be formalized as the instance `PureStrategy (NashDemandStrategies 0.5 ... ...)`.

We then represent a Mixed Strategy as:

```lean
structure MixedStrategy (A : Type) :=
  (strategies: List (PureStrategy A))
  (probabilities: List Rat)
  (probabilities_sum_to_one: List.foldl (a + b) 0 probabilities = 1)
  (probabilities_non_negative: List.all probabilities (λ p => p > 0))
  (same_length: List.length strategies = List.length probabilities)
```

which defines a Mixed Strategy as a list of Pure Strategies and a list of probabilities, as well as constraints on those lists.

Then, a Strategy is defined as either a Pure Strategy or a Mixed Strategy:

```lean
inductive Strategy (A : Type) where
| pure : PureStrategy A → Strategy A
| mixed : MixedStrategy A → Strategy A
```

A Strategy Profile, which is a list of strategies, is then defined as:

```lean
structure StrategyProfile (L: List Type) where
  (strategies: (i: Fin (List.length L)) → Strategy (List.get L i))
```

The reason that this must be a function from a natural number to a strategy is that the strategies for each player must be of different types. For example, in the Ultimatum Game, the first player's strategy is a real number between 0 and 1, while the second player's strategy is a essentially a reject or accept answer.

A Utility Profile, which is a list of utilities, is then defined as:

```lean
structure UtilityProfile (L: List Type) where
  (utilities: List Rat)
  (same_length: List.length L = List.length utilities)
```

And the Utility Function is defined as:

```lean
inductive UtilityFunction (L: List Type) where
  | mk (x: PureStrategyProfile L → UtilityProfile L) : UtilityFunction L
```

which essentially maps a pure strategy profile to a utility profile. To map a full strategy profile (i.e. one including mixed strategies) to a utility profile, you use UtilityProfile.apply, which automatically converts a pure function into a mixed one:

```lean
@[aesop norm unfold]
def UtilityFunction.apply : UtilityFunction L → L.length > 0 → PureStrategyProfile L → StrategyProfile L → UtilityProfile L
  | mk x => λ l psp sp => eval_sp sp x psp ⟨0, l⟩
```

One thing to note is that this process of automatic conversion, though not very computationally taxing, is quite taxing for proof writing, as it makes statements become quite large.

Finally, a Game is defined as:

```lean
structure Game (L: List Type) (N: Nat) where
  (utility: UtilityFunction L)
  (same_length: (List.length L) = N)
  (at_least_one_player: N > 0)
  (pure_strategy_profile: PureStrategyProfile L)
```

and an instance of a Game is defined as:

```lean
def PlayGame (L: List Type) (N: Nat) (G: Game L N) (S: StrategyProfile L) : UtilityProfile L :=
  G.utility.apply
    (by simp_all only [gt_iff_lt]
        obtain ⟨_, same_length, at_least_one_player, _⟩ := G
        subst same_length
        simp_all only [gt_iff_lt])
    (by exact G.pure_strategy_profile)
    S
```

which applies the utility function of the game to a given strategy profile to get a utility profile.

We also define a property of a Strategy Profile being a Nash Equilibrium as:

```lean
def NashEquilibrium (L: List Type) (N: Nat) (G: Game L N) (S: StrategyProfile L) : Prop :=
  ∀ (S': StrategyProfile L)
    (delta: Fin (List.length L)),
    UnilateralChange L S S' delta → DoesAtLeastAsWellAs L N G S S' delta
```

which essentially states that, for each player, and for each strategy that the player could switch to, the utility of that player in the new strategy is less than or equal to their utility in the original strategy profile.

## Example: Prisoner's Dilemma

The Prisoner's Dilemma is a classic game in Game Theory. It is a two-player game where each player can either cooperate or defect. An example payoff matrix which fits the definition of Prisoner's Dilemma is:

| Player 1 / Player 2 | Cooperate | Defect |
| ------------------- | --------- | ------ |
| Cooperate           | 3, 3      | 1, 4   |
| Defect              | 4, 1      | 2, 2   |

We created an example formalization of the Prisoner's Dilemma in Lean as follows:

```lean
inductive PrisonersDilemmaStrategies where
| silent
| confess

def PL : List Type := [PrisonersDilemmaStrategies, PrisonersDilemmaStrategies]

def PL_length : List.length PL = 2 := rfl

def PrisonersDilemmaUtilityFunction : UtilityFunction PL :=
  ⟨λ S => match (S.strategies (Fin.ofNat 0)).val, (S.strategies (Fin.ofNat 1)).val with
          | PrisonersDilemmaStrategies.silent,  PrisonersDilemmaStrategies.silent  => { utilities := [3, 3], same_length := rfl }
          | PrisonersDilemmaStrategies.silent,  PrisonersDilemmaStrategies.confess => { utilities := [1, 4], same_length := rfl }
          | PrisonersDilemmaStrategies.confess, PrisonersDilemmaStrategies.silent  => { utilities := [4, 1], same_length := rfl }
          | PrisonersDilemmaStrategies.confess, PrisonersDilemmaStrategies.confess => { utilities := [2, 2], same_length := rfl }
  ⟩

def PrisonersDilemmaPureProfile : PureStrategyProfile PL :=
  { strategies := λ i => match i with
                          | ⟨0, _⟩ => ⟨PrisonersDilemmaStrategies.silent⟩
                          | ⟨1, _⟩ => ⟨PrisonersDilemmaStrategies.silent⟩
  }

def PrisonersDilemmaSilentSilentProfile : StrategyProfile PL :=
  { strategies := λ i => match i with
                          | ⟨0, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.silent⟩
                          | ⟨1, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.silent⟩
  }

def PrisonersDilemmaSilentConfessProfile : StrategyProfile PL :=
  { strategies := λ i => match i with
                          | ⟨0, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.silent⟩
                          | ⟨1, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.confess⟩
  }

def PrisonersDilemmaConfessConfessProfile : StrategyProfile PL :=
  { strategies := λ i => match i with
                          | ⟨0, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.confess⟩
                          | ⟨1, _⟩ => Strategy.pure ⟨PrisonersDilemmaStrategies.confess⟩
  }

def PrisonersDilemmaGame : Game PL 2 :=
{ utility := PrisonersDilemmaUtilityFunction,
  same_length := rfl,
  at_least_one_player := Nat.zero_lt_succ 1
  pure_strategy_profile := by exact PrisonersDilemmaPureProfile
}
```

This formalization defines the type `PrisonersDilemmaStrategies` to be the type of strategies for the Prisoner's Dilemma, and defines the list `PL` to be the Strategy to Player mapping. It then defines the utility function for the Prisoner's Dilemma by matching on the strategies of the two players and returning the appropriate utility profile. Finally, it defines the Prisoner's Dilemma game as a game with the Prisoner's Dilemma utility function, 2 players, and a proof that there is at least one player.

You can then prove that (silent, silent) is not a nash equilibrium as follows:
```lean
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
```

The second theorem here is the important one, actually showing that (silent, silent) is not a nash equilibrium. The proof operates by applying a theorem stating that, if any unilateral change (a profile with only a single player changing) performs better than the given strategy, it's not a nash equilibrium. Then we just have to show that we have a unilateral change and that that unilateral change performs better than (silent, silent). For the purposes of this proof, I chose to show that (silent, confess) is this unilateral change. 

The case a.left is where we show that (silent, confess) is a unilateral change of (silent, silent), and we delegate that to the first theorem, which essentially shows that fact by manual brute force. The case a.right is where we show (silent, confess) is better for the second player than (silent, silent), which is shown by unwrapping all of our definitions and reducing to the actual inequality that they represent: 3 < 4.

## Example: Rock, Paper, Scissors

Rock, Paper, Scissors is another classic game. It's a two-player game with 3 strategies for each player. An example payoff matrix which fits the definition of Rock, Paper, Scissors is:

| Player 1 / Player 2 | Rock | Paper | Scissors |
| ------------------- | ---- | ----- | -------- |
| Rock                | 1, 1 | 0, 2  | 2, 0     |
| Paper               | 2, 0 | 1, 1  | 0, 2     |
| Scissors            | 0, 2 | 2, 0  | 1, 1     |

We created an example formalization of Rock, Paper, Scissors in Lean as follows:

```lean
inductive RockPaperScissorsStrategies where
| rock
| paper
| scissors

def RPS : List Type := [RockPaperScissorsStrategies, RockPaperScissorsStrategies]
def RPS_length : List.length RPS = 2 := rfl

def RockPaperScissorsUtilityFunction : UtilityFunction RPS :=
  { val := λ S => match S.strategies (Fin.ofNat 0), S.strategies (Fin.ofNat 1) with
                  | Strategy.pure s1, Strategy.pure s2 =>
                    have h1 : PureStrategy (List.get RPS (Fin.ofNat 0)) = PureStrategy RockPaperScissorsStrategies := rfl
                    have h2 : PureStrategy (List.get RPS (Fin.ofNat 1)) = PureStrategy RockPaperScissorsStrategies := rfl
                    let s1' : PureStrategy RockPaperScissorsStrategies := by { rw [←h1]; exact s1 }
                    let s2' : PureStrategy RockPaperScissorsStrategies := by { rw [←h2]; exact s2 }
                    match s1'.val, s2'.val with
                    | RockPaperScissorsStrategies.rock,     RockPaperScissorsStrategies.rock     => { utilities := [1, 1], same_length := rfl }
                    | RockPaperScissorsStrategies.rock,     RockPaperScissorsStrategies.paper    => { utilities := [0, 2], same_length := rfl }
                    | RockPaperScissorsStrategies.rock,     RockPaperScissorsStrategies.scissors => { utilities := [2, 0], same_length := rfl }
                    | RockPaperScissorsStrategies.paper,    RockPaperScissorsStrategies.rock     => { utilities := [2, 0], same_length := rfl }
                    | RockPaperScissorsStrategies.paper,    RockPaperScissorsStrategies.paper    => { utilities := [1, 1], same_length := rfl }
                    | RockPaperScissorsStrategies.paper,    RockPaperScissorsStrategies.scissors => { utilities := [0, 2], same_length := rfl }
                    | RockPaperScissorsStrategies.scissors, RockPaperScissorsStrategies.rock     => { utilities := [0, 2], same_length := rfl }
                    | RockPaperScissorsStrategies.scissors, RockPaperScissorsStrategies.paper    => { utilities := [2, 0], same_length := rfl }
                    | RockPaperScissorsStrategies.scissors, RockPaperScissorsStrategies.scissors => { utilities := [1, 1], same_length := rfl }
                  | _, _ => { utilities := [0, 0], same_length := rfl }
  }

def RockPaperScissorsGame : Game RPS 2 :=
  { utility := RockPaperScissorsUtilityFunction,
    same_length := rfl,
    at_least_one_player := Nat.zero_lt_succ 1
  }
```

This formalization defines the type `RockPaperScissorsStrategies` to be the type of strategies for Rock, Paper, Scissors, and defines the list `RPS` to be the Strategy to Player mapping. It then defines the utility function for Rock, Paper, Scissors by matching on the strategies of the two players and returning the appropriate utility profile. Finally, it defines the Rock, Paper, Scissors game as a game with the Rock, Paper, Scissors utility function, 2 players, and a proof that there is at least one player.

## Example: Nash Demand Game

Our last example is the Nash Demand Game. It's a two-player game where each player can demand a real number between 0 and 1. If the sum of the demands is greater than 1, then both players get 0. Otherwise, the first player gets their demand and the second player gets theirs.

We created an example formalization of the Nash Demand Game in Lean as follows:

```lean
structure NashDemandChoice where
  (demand: Real)
  (demand_nonnegative: demand ≥ 0)
  (demand_le_one: demand ≤ 1)

def NashDemandChoiceList : List Type := [NashDemandChoice, NashDemandChoice]

noncomputable def NashDemandUtilityFunction : UtilityFunction NashDemandChoiceList :=
  { val := λ S => match S.strategies (Fin.ofNat 0), S.strategies (Fin.ofNat 1) with
                  | Strategy.pure s1, Strategy.pure s2 =>
                    have h1 : PureStrategy (List.get NashDemandChoiceList (Fin.ofNat 0)) = PureStrategy NashDemandChoice := rfl
                    have h2 : PureStrategy (List.get NashDemandChoiceList (Fin.ofNat 1)) = PureStrategy NashDemandChoice := rfl
                    let s1' : PureStrategy NashDemandChoice := by { rw [←h1]; exact s1 }
                    let s2' : PureStrategy NashDemandChoice := by { rw [←h2]; exact s2 }
                    match s1', s2' with
                    | ⟨d1, _, _⟩, ⟨d2, _, _⟩ =>
                      let d12 : Utility := ⟨d1 + d2⟩
                      let oneUtility : Utility := ⟨1⟩
                        if d12 ≤ oneUtility then { utilities := [⟨d1⟩, ⟨d2⟩], same_length := rfl }
                      else { utilities := [0, 0], same_length := rfl }
                  | _, _ => { utilities := [0, 0], same_length := rfl }
  }

noncomputable def NashDemandGame : Game NashDemandChoiceList 2 :=
  { utility := NashDemandUtilityFunction,
    same_length := rfl,
    at_least_one_player := Nat.zero_lt_succ 1
  }
```

This formalization defines the type `NashDemandChoice` to be the type of strategies for the Nash Demand Game, and defines the list `NashDemandChoiceList` to be the Strategy to Player mapping. It then defines the utility function for the Nash Demand Game by matching on the strategies of the two players and returning the appropriate utility profile. Because of some properties of Real numbers defined using Cauchy sequences, the definitions must be marked `noncomputable`, meaning they can be used in proofs, but not directly calculated. Finally, it defines the Nash Demand Game as a game with the Nash Demand utility function, 2 players, and a proof that there is at least one player.

## Conclusion

This repository contains an example of formal structures and properties to represent and reason about games in Lean. While there have been other attempts to make such a formalization, the representation proposed here is novel in that it can represent a much broader class of games than previous attempts. In particular, this formalization is able to represent games with more than 2 players, games with a continuous set of actions, and games with intricate utility functions.