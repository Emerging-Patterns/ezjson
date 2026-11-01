# proofs of laws/SkipFailsWhereNoValue.bend
import Base
import ../src/lex.bend as Lex
import ../src/pull.bend as Pull
import ../laws/SkipFailsWhereNoValue.bend as Laws
import ../laws/defs/CursorAndNumberRules.bend as D1
import ./lemmas/LexemeOrder.bend as M1
import ./lemmas/LexerPunctuation.bend as M2

def Laws.pull_over_skip(_rest, _stack, bad):
  match bad:
    case True{}:
      {==}
    case False{}:
      {==}

# the cursor steps over whitespace between tokens, keeping its state, from
# one character on, the rest given
law go_ws.cons:
  for +ff: Nat
  for +uu: U32
  for +tl: String
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +goal: Pull.Goal
  for got: ({D1.is_ws(Chr{uu}) == True{} : Bool} & {D1.all_ws(tl) == True{} : Bool})
  for ih: {D1.all_ws(tl) == True{} : Bool}
    -> {Pull.next.go(1n+ff, tl ++ tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}})
      == Pull.next.go(1n+ff, tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}}) : Pull.Out}
  {Pull.next.go(1n+ff, SCon{Chr{uu}, tl ++ tail}, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}})
    == Pull.next.go(1n+ff, tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}}) : Pull.Out}

def go_ws.cons(ff, uu, tl, tail, stack, goal, got, ih):
  (e1, e2) = got
  cls = Equal.sym(Lex.Class, Lex.classify(Chr{uu}), Lex.CSpace{}, M2.ws_a(uu, U32.is_eq(uu, 32), {==}, e1))
  %cls : {Pull.next.go(1n+ff, tl ++ tail, Pull.look.plan(Chr{uu}, stack, goal, False{}, _))
    == Pull.next.go(1n+ff, tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}}) : Pull.Out}
  ih(e2)

# the cursor steps over whitespace between tokens, keeping its state
law go_ws:
  for +ff: Nat
  for +ws: String
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +goal: Pull.Goal
  for h_ws: {D1.all_ws(ws) == True{} : Bool}
  {Pull.next.go(1n+ff, ws ++ tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}})
    == Pull.next.go(1n+ff, tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}}) : Pull.Out}

def go_ws(ff, ws, tail, stack, goal, h_ws):
  match ws:
    case SNil{}:
      {==}
    case SCon{Chr{+uu}, +tl}:
      go_ws.cons(ff, uu, tl, tail, stack, goal, M1.and_both(D1.is_ws(Chr{uu}), D1.all_ws(tl), h_ws),
        hh => go_ws(ff, tl, tail, stack, goal, hh))

# a walk steps over whitespace between tokens, keeping its state
law walk_ws:
  for +ws: String
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +goal: Pull.Goal
  for h_ws: {D1.all_ws(ws) == True{} : Bool}
  {Pull.next.walk(ws ++ tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}})
    == Pull.next.walk(tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}}) : (Pull.Stop & Pull.Cur)}

def walk_ws(ws, tail, stack, goal, h_ws):
  Equal.cong(Pull.Out, (Pull.Stop & Pull.Cur), xx => Pull.next.fin(Pull.next.grow(32n, 1n, xx)),
    Pull.next.go(4n, ws ++ tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}}),
    Pull.next.go(4n, tail, Pull.S{Pull.MIdle{}, stack, goal, False{}, False{}}),
    go_ws(3n, ws, tail, stack, goal, h_ws))

def Laws.skip_key(ws, key, fresh, stack, h_ws):
  we = Equal.sym((Pull.Stop & Pull.Cur),
    Pull.next.walk(ws ++ SCon{'"', key},
      Pull.S{Pull.MIdle{}, Pull.FObj{Pull.SKey{}, fresh} <> stack, Pull.GSkip{0n}, False{}, False{}}),
    Pull.next.walk(SCon{'"', key},
      Pull.S{Pull.MIdle{}, Pull.FObj{Pull.SKey{}, fresh} <> stack, Pull.GSkip{0n}, False{}, False{}}),
    walk_ws(ws, SCon{'"', key}, Pull.FObj{Pull.SKey{}, fresh} <> stack, Pull.GSkip{0n}, h_ws))
  %we : {Pull.skip.use(_) == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
  gd = Equal.sym(Pull.Out, Pull.next.go(4n, key, Pull.err.st(Pull.GSkip{0n})),
    Pull.Fin{(Pull.SEv{Pull.EErr{}}, Pull.Cur{"", [], False{}, True{}})},
    M2.go_done(3n, key, Pull.SEv{Pull.EErr{}}, "", [], Pull.GSkip{0n}, False{}, True{}))
  %gd : {Pull.skip.use(Pull.next.fin(Pull.next.grow(32n, 1n, _))) == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
  {==}

# the parent after a close, in a top-level skip, is a failure
law close_out_err:
  for ev: Pull.Ev
  for frames: List<&2, Pull.Frame>
  {Pull.close.out(ev, frames, Pull.GSkip{0n}) == Pull.err.st(Pull.GSkip{0n}) : Pull.St}

def close_out_err(_ev, frames):
  match frames:
    case Nil{}:
      {==}
    case Pull.FArr{Pull.SVal{}, _} <> _:
      {==}
    case Pull.FArr{Pull.SCom{}, _} <> _:
      {==}
    case Pull.FArr{Pull.SKey{}, _} <> _:
      {==}
    case Pull.FArr{Pull.SCol{}, _} <> _:
      {==}
    case Pull.FObj{Pull.SVal{}, _} <> _:
      {==}
    case Pull.FObj{Pull.SCom{}, _} <> _:
      {==}
    case Pull.FObj{Pull.SKey{}, _} <> _:
      {==}
    case Pull.FObj{Pull.SCol{}, _} <> _:
      {==}

# a close in a top-level skip is a failure, whatever is open
law close_arr_err:
  for stack: List<&2, Pull.Frame>
  {Pull.close.arr(stack, Pull.GSkip{0n}) == Pull.err.st(Pull.GSkip{0n}) : Pull.St}

def close_arr_err(stack):
  match stack:
    case Nil{}:
      {==}
    case Pull.FArr{Pull.SVal{}, True{}} <> frames:
      close_out_err(Pull.EEndArr{}, frames)
    case Pull.FArr{Pull.SVal{}, False{}} <> _:
      {==}
    case Pull.FArr{Pull.SCom{}, True{}} <> frames:
      close_out_err(Pull.EEndArr{}, frames)
    case Pull.FArr{Pull.SCom{}, False{}} <> frames:
      close_out_err(Pull.EEndArr{}, frames)
    case Pull.FArr{Pull.SKey{}, True{}} <> _:
      {==}
    case Pull.FArr{Pull.SKey{}, False{}} <> _:
      {==}
    case Pull.FArr{Pull.SCol{}, True{}} <> _:
      {==}
    case Pull.FArr{Pull.SCol{}, False{}} <> _:
      {==}
    case Pull.FObj{Pull.SVal{}, True{}} <> _:
      {==}
    case Pull.FObj{Pull.SVal{}, False{}} <> _:
      {==}
    case Pull.FObj{Pull.SCom{}, True{}} <> _:
      {==}
    case Pull.FObj{Pull.SCom{}, False{}} <> _:
      {==}
    case Pull.FObj{Pull.SKey{}, True{}} <> _:
      {==}
    case Pull.FObj{Pull.SKey{}, False{}} <> _:
      {==}
    case Pull.FObj{Pull.SCol{}, True{}} <> _:
      {==}
    case Pull.FObj{Pull.SCol{}, False{}} <> _:
      {==}

def Laws.skip_close_arr(ws, rest, stack, h_ws):
  we = Equal.sym((Pull.Stop & Pull.Cur),
    Pull.next.walk(ws ++ SCon{']', rest}, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{0n}, False{}, False{}}),
    Pull.next.walk(SCon{']', rest}, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{0n}, False{}, False{}}),
    walk_ws(ws, SCon{']', rest}, stack, Pull.GSkip{0n}, h_ws))
  %we : {Pull.skip.use(_) == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
  ce = Equal.sym(Pull.St, Pull.close.arr(stack, Pull.GSkip{0n}), Pull.err.st(Pull.GSkip{0n}), close_arr_err(stack))
  %ce : {Pull.skip.use(Pull.next.fin(Pull.next.grow(32n, 1n, Pull.next.go(4n, rest, _))))
    == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
  gd = Equal.sym(Pull.Out, Pull.next.go(4n, rest, Pull.err.st(Pull.GSkip{0n})),
    Pull.Fin{(Pull.SEv{Pull.EErr{}}, Pull.Cur{"", [], False{}, True{}})},
    M2.go_done(3n, rest, Pull.SEv{Pull.EErr{}}, "", [], Pull.GSkip{0n}, False{}, True{}))
  %gd : {Pull.skip.use(Pull.next.fin(Pull.next.grow(32n, 1n, _))) == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
  {==}

# a close in a top-level skip is a failure, whatever is open
law close_obj_err:
  for stack: List<&2, Pull.Frame>
  {Pull.close.obj(stack, Pull.GSkip{0n}) == Pull.err.st(Pull.GSkip{0n}) : Pull.St}

def close_obj_err(stack):
  match stack:
    case Nil{}:
      {==}
    case Pull.FArr{Pull.SVal{}, True{}} <> _:
      {==}
    case Pull.FArr{Pull.SVal{}, False{}} <> _:
      {==}
    case Pull.FArr{Pull.SCom{}, True{}} <> _:
      {==}
    case Pull.FArr{Pull.SCom{}, False{}} <> _:
      {==}
    case Pull.FArr{Pull.SKey{}, True{}} <> _:
      {==}
    case Pull.FArr{Pull.SKey{}, False{}} <> _:
      {==}
    case Pull.FArr{Pull.SCol{}, True{}} <> _:
      {==}
    case Pull.FArr{Pull.SCol{}, False{}} <> _:
      {==}
    case Pull.FObj{Pull.SVal{}, True{}} <> _:
      {==}
    case Pull.FObj{Pull.SVal{}, False{}} <> _:
      {==}
    case Pull.FObj{Pull.SCom{}, True{}} <> frames:
      close_out_err(Pull.EEndObj{}, frames)
    case Pull.FObj{Pull.SCom{}, False{}} <> frames:
      close_out_err(Pull.EEndObj{}, frames)
    case Pull.FObj{Pull.SKey{}, True{}} <> frames:
      close_out_err(Pull.EEndObj{}, frames)
    case Pull.FObj{Pull.SKey{}, False{}} <> _:
      {==}
    case Pull.FObj{Pull.SCol{}, True{}} <> _:
      {==}
    case Pull.FObj{Pull.SCol{}, False{}} <> _:
      {==}

def Laws.skip_close_obj(ws, rest, stack, h_ws):
  we = Equal.sym((Pull.Stop & Pull.Cur),
    Pull.next.walk(ws ++ SCon{'}', rest}, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{0n}, False{}, False{}}),
    Pull.next.walk(SCon{'}', rest}, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{0n}, False{}, False{}}),
    walk_ws(ws, SCon{'}', rest}, stack, Pull.GSkip{0n}, h_ws))
  %we : {Pull.skip.use(_) == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
  ce = Equal.sym(Pull.St, Pull.close.obj(stack, Pull.GSkip{0n}), Pull.err.st(Pull.GSkip{0n}), close_obj_err(stack))
  %ce : {Pull.skip.use(Pull.next.fin(Pull.next.grow(32n, 1n, Pull.next.go(4n, rest, _))))
    == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
  gd = Equal.sym(Pull.Out, Pull.next.go(4n, rest, Pull.err.st(Pull.GSkip{0n})),
    Pull.Fin{(Pull.SEv{Pull.EErr{}}, Pull.Cur{"", [], False{}, True{}})},
    M2.go_done(3n, rest, Pull.SEv{Pull.EErr{}}, "", [], Pull.GSkip{0n}, False{}, True{}))
  %gd : {Pull.skip.use(Pull.next.fin(Pull.next.grow(32n, 1n, _))) == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
  {==}
