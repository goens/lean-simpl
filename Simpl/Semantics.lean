import Simpl.Syntax
import Std
import Lean
namespace Simpl

abbrev Record := Std.HashMap
abbrev CVal := UInt32
instance : Repr $ Record Lean.Name CVal where
  reprPrec r prec := reprPrec (r.toList) prec

inductive Status where
  | Normal : Status
  | Abrupt : Status
  | Stuck : Status
  | Fault : Status

  deriving Inhabited, Repr
structure State where
  (local_variables : Record Lean.Name CVal)
  (global_variables : Record Lean.Name CVal)
  deriving Inhabited, Repr

/-
  The main reason why we build our own syntax types, instead of using the Lean ones (i.e. TSyntax `nonterminal) is that we can't build new syntax terms without going into some monad (like Lean.MonadQuotation). See for example what happens with:
```
#check `(expression| 1 + 2)
```
yields:
```
do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let scp ← Lean.getCurrMacroScope
  let mainModule ← Lean.getMainModule
  pure
      {
        raw :=
          Lean.Syntax.node3 info `Simpl.expression_+_
            (Lean.Syntax.node1 info `Simpl.expression_ (Lean.Syntax.node1 info `num (Lean.Syntax.atom info "1")))
            (Lean.Syntax.atom info "+")
            (Lean.Syntax.node1 info `Simpl.expression_
              (Lean.Syntax.node1 info `num (Lean.Syntax.atom info "2"))) } : ?m.876 (Lean.TSyntax `expression)
```

We can't thus define eval recursively by just saying
```
  `(expression| $i + $j) => eval `(expression| $i) + eval `(expression| $j)
```
because we can't build the new syntax terms for recursive functions, like so:

mutual
def eval  : State → (Lean.TSyntax `statement) → State
  | state, Statement.skip => state
  | state, `(statement| $i:ident :== $e) =>
    let new_local_variables := state.local_variables.insert i (eval_expr state e)
    { state with local_variables := new_local_variables }
  | state, `(statement| SKIP) => state
  | state, _ => state

def eval_expr : State → (Lean.TSyntax `expr) → CVal
  | state, `(expression| $i:ident) => state.local_variables.findD i.getId 0
  | state, `(expression| $n:num) => n.getNat.toUInt32
  | state, _ => 0
end

-/


inductive EvalExpr : State → Expression → CVal → Prop
  | lookup : EvalExpr state (Expression.ident i)  (state.local_variables.findD i 0)
  | const : EvalExpr _ (Expression.num n) (n.toUInt32)
  | add : EvalExpr state e₁ v₁ → EvalExpr state e₂ v₂ → EvalExpr state  (Expression.add e₁ e₂) (v₁ + v₂)
  | sub : EvalExpr state e₁ v₁ → EvalExpr state e₂ v₂ → EvalExpr state  (Expression.sub e₁ e₂) (v₁ - v₂)

-- See: https://leanprover.github.io/lean4/doc/examples/tc.lean.html
-- eval won't work as function without coinduction
inductive Step : State × Statement → State × Statement → Prop
  | skip :  Step (state, Statement.skip) (state, Statement.skip)
  | assign : EvalExpr state e v → Step (state, Statement.assign i e) ({ state with local_variables := state.local_variables.insert i v}, Statement.skip)
  | seq_skip : Step (state, Statement.seq (Statement.skip) s₂) (state,s₂)
  | seq_step : Step (state, s₁) (state', s₁') → Step (state, Statement.seq s₁ s₂) (state', Statement.seq s₁' s₂)
  | conditional_true : EvalExpr state e val → val ≠ 0 → Step (state, Statement.conditional e s₁ s₂) (state, s₁)
  | conditional_false : EvalExpr state e val → val = 0 → Step (state, Statement.conditional e s₁ s₂) (state, s₁)
  | while_stop : EvalExpr state e val → val = 0 → Step (state, Statement.while e s) (state, Statement.skip)
  | while_loop : EvalExpr state e val → val ≠ 0 → Step (state, (Statement.while e s)) (state, Statement.seq s (Statement.while e s))
-- Removed because of unspported syntax: elaboration function for 'Lean.Parser.Term.namedPattern' has not been implemented w@(Statement.while e s)
--  | while_loop : EvalExpr state e val → val ≠ 0 → Step (state, w@(Statement.while e s)) (state, Statement.seq s w)
  /- Ignore throw, trycatch, guard, call for now
  | s@(_, Statement.throw _) => s
  | (state, Statement.trycatch t c) => match step (state,t) with
    | (state', Statement.skip) => (state', Statement.skip)
    | (state', Statement.throw e) => step (state', Statement.seq (Statement.assign `exception e) c)
    | (state', t') => (state', t)
  | (state, Statement.guard e₁ e₂ s₁) => (state, Statement.skip) -- TODO: implement
  | (state, Statement.call _) => (state, Statement.skip) -- TODO: implement
  -/

-- An issue here is that `Decidable` requires us to give `cval`, whereas we want to compute it.
def evalExpr (state : State) (e : Expression) : CVal :=
  match e with
  | Expression.ident i => state.local_variables.findD i 0
  | Expression.num n => n.toUInt32
  | Expression.add e₁ e₂ => evalExpr state e₁ + evalExpr state e₂
  | Expression.sub e₁ e₂ => evalExpr state e₁ - evalExpr state e₂

-- Similar to idea from Kyle Miller: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Hypothesis.20in.20.60match.60/near/328812446
theorem evalExpr_correct (state : State) (e : Expression) (cval : CVal) : EvalExpr state e cval ↔ (cval = evalExpr state e) :=
  by
   constructor
   -- =>
   · intro hCval
     induction hCval <;> simp [evalExpr]
     -- case mp.sub
     case mp.sub h₁ h₂ =>
       rw [h₁, h₂]
     case mp.add h₁ h₂ =>
       rw [h₁, h₂]
   -- <=
   · intro hEval
     induction e generalizing cval <;> simp [evalExpr] at hEval <;> simp [hEval]
      -- case mp.sub
     case num n =>
        exact EvalExpr.const
     case ident i =>
        exact EvalExpr.lookup
     case add e₁ e₂ ih_1 ih_2 =>
        have v₁rfl : evalExpr state e₁ = evalExpr state e₁ := rfl
        have hv₁ := ih_1 (evalExpr state e₁) v₁rfl
        have v₂rfl : evalExpr state e₂ = evalExpr state e₂ := rfl
        have hv₂ := ih_2 (evalExpr state e₂) v₂rfl
        exact EvalExpr.add hv₁ hv₂
     case sub e₁ e₂ ih_1 ih_2 =>
        have v₁rfl : evalExpr state e₁ = evalExpr state e₁ := rfl
        have hv₁ := ih_1 (evalExpr state e₁) v₁rfl
        have v₂rfl : evalExpr state e₂ = evalExpr state e₂ := rfl
        have hv₂ := ih_2 (evalExpr state e₂) v₂rfl
        exact EvalExpr.sub hv₁ hv₂

instance (state : State) (e : Expression) (cval : CVal) : Decidable (EvalExpr state e cval) :=
  if h : cval = evalExpr state e
    then isTrue <| by
      exact evalExpr_correct state e cval |>.mpr h
    else isFalse <| by rwa [evalExpr_correct]

def evalStep  : State × Statement → State × Statement
  | (state, Statement.skip) => (state, Statement.skip)
  | (state, Statement.assign name expr) =>
    let state' := {state with local_variables := state.local_variables.insert name (evalExpr state expr)}
    (state', Statement.skip)
--  | (state, Statement.seq (Statement.skip) s₂) => (state, s₂)
  | (state, Statement.seq s₁ s₂) => match evalStep (state, s₁) with
    | (state', Statement.skip) => (state', s₂)
    | (state', s₁') => (state', Statement.seq s₁' s₂)
  | (state, Statement.conditional e s₁ s₂) => if evalExpr state e ≠ 0 then (state, s₁) else (state, s₂)
  | (state, Statement.while e s) => if (evalExpr state e) ≠ 0 then (state, Statement.seq s (Statement.while e s)) else (state, Statement.skip)
  -- TODO: throw, trycatch, guard, call
  | (state, _) => (state, Statement.skip)

partial def eval (s : Statement) (state : State := default) : State :=
  match evalStep (state, s) with
  | (state', Statement.skip) => state'
  | (state', s') => eval s' state'

def test := [simpl|
  X :== 10;
  Y :== 1;
  WHILE X DO
    X :== X - 1;
    Y :== Y + Y
  OD
]

#eval eval test
end Simpl
