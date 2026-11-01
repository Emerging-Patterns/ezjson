# proofs of laws/CursorEventsMatchParse.bend
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../src/lex.bend as Lex
import ../src/parse.bend as Parse
import ../src/pull.bend as Pull
import ../laws/CursorEventsMatchParse.bend as Laws
import ../laws/NumOkIsNumberRule.bend as L1
import ../laws/ParsesExactlyJsonTexts.bend as L2
import ../laws/defs/CursorAndNumberRules.bend as D1
import ../laws/defs/GrammarDerivations.bend as D2
import ./lemmas/ArrayLength.bend as M1
import ./lemmas/CharacterClasses.bend as M2
import ./lemmas/CharacterScan.bend as M3
import ./lemmas/CursorFollowsDerivation.bend as M4
import ./lemmas/DerivationText.bend as M5
import ./lemmas/LexemeOrder.bend as M6
import ./lemmas/LexerBuildsDerivations.bend as M7
import ./lemmas/LexerPunctuation.bend as M8
import ./lemmas/NumberCharsAreWordChars.bend as M9
import ./lemmas/NumberDigits.bend as M10
import ./lemmas/OwnedParse.bend as M11
import ./lemmas/ParserReadsTokens.bend as M12
import ./lemmas/StringPieceLexing.bend as M13
import ./lemmas/StringTokens.bend as M14
import ./lemmas/WellFormedCells.bend as M15
import ./lemmas/WordArithmetic.bend as M16
import ./lemmas/WordLexing.bend as M17

# laws/CursorEventsMatchParse.bend: the cursor on a derivation's text

# a step that already stopped on the suffix in hand returns it
law go_rest:
  for +ff: Nat
  for +txt: String
  for stop: Pull.Stop
  for stack: List<&2, Pull.Frame>
  for goal: Pull.Goal
  for done: Bool
  for bad: Bool
  {Pull.next.go(1n+ff, txt, Pull.S{Pull.MRest{stop}, stack, goal, done, bad})
    == Pull.Fin{(stop, Pull.Cur{txt, stack, done, bad})} : Pull.Out}

def go_rest(_ff, txt, _stop, _stack, _goal, _done, _bad):
  match txt:
    case SNil{}:
      {==}
    case SCon{_, _}:
      {==}

# the cursor steps over whitespace between tokens, keeping its state, from
# one character on, the rest given, whether or not the root is over
law go_wsd.cons:
  for +ff: Nat
  for +uu: U32
  for +tl: String
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +goal: Pull.Goal
  for +done: Bool
  for got: ({D1.is_ws(Chr{uu}) == True{} : Bool} & {D1.all_ws(tl) == True{} : Bool})
  for ih: {D1.all_ws(tl) == True{} : Bool}
    -> {Pull.next.go(1n+ff, tl ++ tail, Pull.S{Pull.MIdle{}, stack, goal, done, False{}})
      == Pull.next.go(1n+ff, tail, Pull.S{Pull.MIdle{}, stack, goal, done, False{}}) : Pull.Out}
  {Pull.next.go(1n+ff, SCon{Chr{uu}, tl ++ tail}, Pull.S{Pull.MIdle{}, stack, goal, done, False{}})
    == Pull.next.go(1n+ff, tail, Pull.S{Pull.MIdle{}, stack, goal, done, False{}}) : Pull.Out}

def go_wsd.cons(ff, uu, tl, tail, stack, goal, done, got, ih):
  (e1, e2) = got
  cls = Equal.sym(Lex.Class, Lex.classify(Chr{uu}), Lex.CSpace{}, M8.ws_a(uu, U32.is_eq(uu, 32), {==}, e1))
  %cls : {Pull.next.go(1n+ff, tl ++ tail, Pull.look.plan(Chr{uu}, stack, goal, done, _))
    == Pull.next.go(1n+ff, tail, Pull.S{Pull.MIdle{}, stack, goal, done, False{}}) : Pull.Out}
  ih(e2)

# the cursor steps over whitespace between tokens, keeping its state
law go_wsd:
  for +ff: Nat
  for +ws: String
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +goal: Pull.Goal
  for +done: Bool
  for h_ws: {D1.all_ws(ws) == True{} : Bool}
  {Pull.next.go(1n+ff, ws ++ tail, Pull.S{Pull.MIdle{}, stack, goal, done, False{}})
    == Pull.next.go(1n+ff, tail, Pull.S{Pull.MIdle{}, stack, goal, done, False{}}) : Pull.Out}

def go_wsd(ff, ws, tail, stack, goal, done, h_ws):
  match ws:
    case SNil{}:
      {==}
    case SCon{Chr{+uu}, +tl}:
      go_wsd.cons(ff, uu, tl, tail, stack, goal, done, M6.and_both(D1.is_ws(Chr{uu}), D1.all_ws(tl), h_ws),
        hh => go_wsd(ff, tl, tail, stack, goal, done, hh))

# next steps over whitespace, whether or not the root is over
law next_ws:
  for +ws: String
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for h_ws: {D1.all_ws(ws) == True{} : Bool}
  {Ezjson.next(Pull.Cur{ws ++ tail, stack, done, False{}}) == Ezjson.next(Pull.Cur{tail, stack, done, False{}})
    : (Pull.Ev & Pull.Cur)}

def next_ws(ws, tail, stack, done, h_ws):
  Equal.cong(Pull.Out, (Pull.Ev & Pull.Cur), xx => Pull.next.use(Pull.next.fin(Pull.next.grow(32n, 1n, xx))),
    Pull.next.go(4n, ws ++ tail, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, done, False{}}),
    Pull.next.go(4n, tail, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, done, False{}}),
    go_wsd(3n, ws, tail, stack, Pull.GNext{}, done, h_ws))

# next, once the first budget's walk is known to have finished
law next_fin:
  for +txt: String
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for got: (Pull.Stop & Pull.Cur)
  for ee: {Pull.next.go(4n, txt, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, done, False{}}) == Pull.Fin{got}
    : Pull.Out}
  {Ezjson.next(Pull.Cur{txt, stack, done, False{}}) == Pull.next.use(got) : (Pull.Ev & Pull.Cur)}

def next_fin(txt, stack, done, got, ee):
  Equal.cong(Pull.Out, (Pull.Ev & Pull.Cur), xx => Pull.next.use(Pull.next.fin(Pull.next.grow(32n, 1n, xx))),
    Pull.next.go(4n, txt, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, done, False{}}), Pull.Fin{got}, ee)

# after the root and whitespace, the text's end is the end
law next_eof:
  for +ws: String
  for +stack: List<&2, Pull.Frame>
  for h_ws: {D1.all_ws(ws) == True{} : Bool}
  {Ezjson.next(Pull.Cur{ws, stack, True{}, False{}}) == (Pull.EEnd{}, Pull.Cur{"", stack, True{}, False{}})
    : (Pull.Ev & Pull.Cur)}

def next_eof(ws, stack, h_ws):
  ea = M6.append_nil(ws)
  %ea : {Ezjson.next(Pull.Cur{_, stack, True{}, False{}}) == (Pull.EEnd{}, Pull.Cur{"", stack, True{}, False{}})
    : (Pull.Ev & Pull.Cur)}
  next_ws(ws, "", stack, True{}, h_ws)

# appending event lists is associative
law eapp_assoc:
  for +aa: List<&2, D1.Evt>
  for +bb: List<&2, D1.Evt>
  for +cc: List<&2, D1.Evt>
  {List.append(&2, D1.Evt, List.append(&2, D1.Evt, aa, bb), cc)
    == List.append(&2, D1.Evt, aa, List.append(&2, D1.Evt, bb, cc)) : List<&2, D1.Evt>}

def eapp_assoc(aa, bb, cc):
  match aa:
    case Nil{}:
      {==}
    case hd <> tl:
      Equal.cong(List<&2, D1.Evt>, List<&2, D1.Evt>, xx => hd <> xx,
        List.append(&2, D1.Evt, List.append(&2, D1.Evt, tl, bb), cc),
        List.append(&2, D1.Evt, tl, List.append(&2, D1.Evt, bb, cc)), eapp_assoc(tl, bb, cc))

# adding is associative
law add_assoc:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  {Nat.add(Nat.add(aa, bb), cc) == Nat.add(aa, Nat.add(bb, cc)) : Nat}

def add_assoc(aa, bb, cc):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(Nat.add(pp, bb), cc), Nat.add(pp, Nat.add(bb, cc)),
        add_assoc(pp, bb, cc))

# adding one is the successor
law add_one:
  for +aa: Nat
  {Nat.add(aa, 1n) == 1n+aa : Nat}

def add_one(aa):
  match aa:
    case 0n:
      {==}
    case 1n+pp:
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 1n), 1n+pp, add_one(pp))

# the length of appended event lists
law len_app:
  for +aa: List<&2, D1.Evt>
  for +bb: List<&2, D1.Evt>
  {List.length(&2, D1.Evt, List.append(&2, D1.Evt, aa, bb))
    == Nat.add(List.length(&2, D1.Evt, aa), List.length(&2, D1.Evt, bb)) : Nat}

def len_app(aa, bb):
  match aa:
    case Nil{}:
      {==}
    case _hd <> tl:
      Equal.cong(Nat, Nat, xx => 1n+xx, List.length(&2, D1.Evt, List.append(&2, D1.Evt, tl, bb)),
        Nat.add(List.length(&2, D1.Evt, tl), List.length(&2, D1.Evt, bb)), len_app(tl, bb))

# the events from `c` start with `es`, after which the cursor is `c2`
def strm(_c: Pull.Cur, _es: List<&2, D1.Evt>, _c2: Pull.Cur) -> Type:
  @nn: Nat -> {D1.pulled(Nat.add(List.length(&2, D1.Evt, _es), nn), _c)
    == List.append(&2, D1.Evt, _es, D1.pulled(nn, _c2)) : List<&2, D1.Evt>}

# one step of next is one event
law strm_one:
  for +c: Pull.Cur
  for +ev: Pull.Ev
  for +c2: Pull.Cur
  for ee: {Ezjson.next(c) == (ev, c2) : (Pull.Ev & Pull.Cur)}
  strm(c, [D1.view(ev)], c2)

def strm_one(c, ev, c2, ee):
  nn => Equal.cong((Pull.Ev & Pull.Cur), List<&2, D1.Evt>,
    xx => D1.view(D1.ev_of(xx)) <> D1.pulled(nn, D1.cur_of(xx)), Ezjson.next(c), (ev, c2), ee)

# strm_app at one count
law strm_app.at:
  for +c: Pull.Cur
  for +aa: List<&2, D1.Evt>
  for +c1: Pull.Cur
  for +bb: List<&2, D1.Evt>
  for +c2: Pull.Cur
  for s1: strm(c, aa, c1)
  for s2: strm(c1, bb, c2)
  for +nn: Nat
  {D1.pulled(Nat.add(List.length(&2, D1.Evt, List.append(&2, D1.Evt, aa, bb)), nn), c)
    == List.append(&2, D1.Evt, List.append(&2, D1.Evt, aa, bb), D1.pulled(nn, c2)) : List<&2, D1.Evt>}

def strm_app.at(c, aa, c1, bb, c2, s1, s2, nn):
  +la = List.length(&2, D1.Evt, aa)
  +lb = List.length(&2, D1.Evt, bb)
  el = Equal.sym(Nat, List.length(&2, D1.Evt, List.append(&2, D1.Evt, aa, bb)), Nat.add(la, lb),
    len_app(aa, bb))
  %el : {D1.pulled(Nat.add(_, nn), c) == List.append(&2, D1.Evt, List.append(&2, D1.Evt, aa, bb),
    D1.pulled(nn, c2)) : List<&2, D1.Evt>}
  ea = Equal.sym(Nat, Nat.add(Nat.add(la, lb), nn), Nat.add(la, Nat.add(lb, nn)), add_assoc(la, lb, nn))
  %ea : {D1.pulled(_, c) == List.append(&2, D1.Evt, List.append(&2, D1.Evt, aa, bb),
    D1.pulled(nn, c2)) : List<&2, D1.Evt>}
  Equal.trans(List<&2, D1.Evt>, D1.pulled(Nat.add(la, Nat.add(lb, nn)), c),
    List.append(&2, D1.Evt, aa, D1.pulled(Nat.add(lb, nn), c1)),
    List.append(&2, D1.Evt, List.append(&2, D1.Evt, aa, bb), D1.pulled(nn, c2)),
    s1(Nat.add(lb, nn)),
    Equal.trans(List<&2, D1.Evt>, List.append(&2, D1.Evt, aa, D1.pulled(Nat.add(lb, nn), c1)),
      List.append(&2, D1.Evt, aa, List.append(&2, D1.Evt, bb, D1.pulled(nn, c2))),
      List.append(&2, D1.Evt, List.append(&2, D1.Evt, aa, bb), D1.pulled(nn, c2)),
      Equal.cong(List<&2, D1.Evt>, List<&2, D1.Evt>, xx => List.append(&2, D1.Evt, aa, xx),
        D1.pulled(Nat.add(lb, nn), c1), List.append(&2, D1.Evt, bb, D1.pulled(nn, c2)), s2(nn)),
      Equal.sym(List<&2, D1.Evt>, List.append(&2, D1.Evt, List.append(&2, D1.Evt, aa, bb),
        D1.pulled(nn, c2)), List.append(&2, D1.Evt, aa, List.append(&2, D1.Evt, bb, D1.pulled(nn, c2))),
        eapp_assoc(aa, bb, D1.pulled(nn, c2)))))

# events one after another
law strm_app:
  for +c: Pull.Cur
  for +aa: List<&2, D1.Evt>
  for +c1: Pull.Cur
  for +bb: List<&2, D1.Evt>
  for +c2: Pull.Cur
  for s1: strm(c, aa, c1)
  for s2: strm(c1, bb, c2)
  strm(c, List.append(&2, D1.Evt, aa, bb), c2)

def strm_app(c, aa, c1, bb, c2, s1, s2):
  nn => strm_app.at(c, aa, c1, bb, c2, s1, s2, nn)

# an event, then more events
law strm_cons:
  for +c: Pull.Cur
  for +ev: Pull.Ev
  for +c1: Pull.Cur
  for +bb: List<&2, D1.Evt>
  for +c2: Pull.Cur
  for ee: {Ezjson.next(c) == (ev, c1) : (Pull.Ev & Pull.Cur)}
  for s2: strm(c1, bb, c2)
  strm(c, D1.view(ev) <> bb, c2)

def strm_cons(c, ev, c1, bb, c2, ee, s2):
  strm_app(c, [D1.view(ev)], c1, bb, c2, strm_one(c, ev, c1, ee), s2)

# a cursor whose next step is another's gives the same events, when there are some
law strm_same:
  for +c: Pull.Cur
  for +c0: Pull.Cur
  for +e0: D1.Evt
  for +es: List<&2, D1.Evt>
  for +c2: Pull.Cur
  for ee: {Ezjson.next(c) == Ezjson.next(c0) : (Pull.Ev & Pull.Cur)}
  for s0: strm(c0, e0 <> es, c2)
  strm(c, e0 <> es, c2)

def strm_same(c, c0, e0, es, c2, ee, s0):
  +nn => Equal.trans(List<&2, D1.Evt>, D1.pulled(1n+Nat.add(List.length(&2, D1.Evt, es), nn), c),
    D1.pulled(1n+Nat.add(List.length(&2, D1.Evt, es), nn), c0),
    List.append(&2, D1.Evt, e0 <> es, D1.pulled(nn, c2)),
    Equal.cong((Pull.Ev & Pull.Cur), List<&2, D1.Evt>,
      xx => D1.view(D1.ev_of(xx)) <> D1.pulled(Nat.add(List.length(&2, D1.Evt, es), nn), D1.cur_of(xx)),
      Ezjson.next(c), Ezjson.next(c0), ee), s0(nn))

# next from one walk equals next from another, once their first budgets agree
law go_next:
  for +x: String
  for +st: List<&2, Pull.Frame>
  for +dd: Bool
  for +y: String
  for +st2: List<&2, Pull.Frame>
  for +dd2: Bool
  for ee: {Pull.next.go(4n, x, Pull.S{Pull.MIdle{}, st, Pull.GNext{}, dd, False{}})
    == Pull.next.go(4n, y, Pull.S{Pull.MIdle{}, st2, Pull.GNext{}, dd2, False{}}) : Pull.Out}
  {Ezjson.next(Pull.Cur{x, st, dd, False{}}) == Ezjson.next(Pull.Cur{y, st2, dd2, False{}}) : (Pull.Ev & Pull.Cur)}

def go_next(x, st, dd, y, st2, dd2, ee):
  Equal.cong(Pull.Out, (Pull.Ev & Pull.Cur), xx => Pull.next.use(Pull.next.fin(Pull.next.grow(32n, 1n, xx))),
    Pull.next.go(4n, x, Pull.S{Pull.MIdle{}, st, Pull.GNext{}, dd, False{}}),
    Pull.next.go(4n, y, Pull.S{Pull.MIdle{}, st2, Pull.GNext{}, dd2, False{}}), ee)

# `[` where a value may go opens an array
law go_open_arr:
  for +x: String
  for +stack: List<&2, Pull.Frame>
  for hs: {True{} == Pull.expect.val.go(stack) : Bool}
  {Pull.next.go(4n, SCon{'[', x}, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, False{}, False{}})
    == Pull.Fin{(Pull.SEv{Pull.EBeginArr{}}, Pull.Cur{x, Pull.FArr{Pull.SVal{}, True{}} <> stack, False{}, False{}})}
    : Pull.Out}

def go_open_arr(x, stack, hs):
  %hs : {Pull.next.go(4n, x, Pull.punct.arr.if(stack, Pull.GNext{}, _))
    == Pull.Fin{(Pull.SEv{Pull.EBeginArr{}}, Pull.Cur{x, Pull.FArr{Pull.SVal{}, True{}} <> stack, False{}, False{}})}
    : Pull.Out}
  go_rest(3n, x, Pull.SEv{Pull.EBeginArr{}}, Pull.FArr{Pull.SVal{}, True{}} <> stack, Pull.GNext{}, False{}, False{})

law next_oarr:
  for +x: String
  for +stack: List<&2, Pull.Frame>
  for h: {Pull.expect.val.go(stack) == True{} : Bool}
  {Ezjson.next(Pull.Cur{SCon{'[', x}, stack, False{}, False{}})
    == (Pull.EBeginArr{}, Pull.Cur{x, Pull.FArr{Pull.SVal{}, True{}} <> stack, False{}, False{}})
    : (Pull.Ev & Pull.Cur)}

def next_oarr(x, stack, h):
  hs = Equal.sym(Bool, Pull.expect.val.go(stack), True{}, h)
  next_fin(SCon{'[', x}, stack, False{}, (Pull.SEv{Pull.EBeginArr{}}, Pull.Cur{x, Pull.FArr{Pull.SVal{},
    True{}} <> stack,
    False{}, False{}}),
    go_open_arr(x, stack, hs))

# `{` where a value may go opens an object
law go_open_obj:
  for +x: String
  for +stack: List<&2, Pull.Frame>
  for hs: {True{} == Pull.expect.val.go(stack) : Bool}
  {Pull.next.go(4n, SCon{'{', x}, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, False{}, False{}})
    == Pull.Fin{(Pull.SEv{Pull.EBeginObj{}}, Pull.Cur{x, Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, False{}})}
    : Pull.Out}

def go_open_obj(x, stack, hs):
  %hs : {Pull.next.go(4n, x, Pull.punct.obj.if(stack, Pull.GNext{}, _))
    == Pull.Fin{(Pull.SEv{Pull.EBeginObj{}}, Pull.Cur{x, Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, False{}})}
    : Pull.Out}
  go_rest(3n, x, Pull.SEv{Pull.EBeginObj{}}, Pull.FObj{Pull.SKey{}, True{}} <> stack, Pull.GNext{}, False{}, False{})

# `{` where a value may go opens an object
law next_oobj:
  for +x: String
  for +stack: List<&2, Pull.Frame>
  for h: {Pull.expect.val.go(stack) == True{} : Bool}
  {Ezjson.next(Pull.Cur{SCon{'{', x}, stack, False{}, False{}})
    == (Pull.EBeginObj{}, Pull.Cur{x, Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, False{}})
    : (Pull.Ev & Pull.Cur)}

def next_oobj(x, stack, h):
  hs = Equal.sym(Bool, Pull.expect.val.go(stack), True{}, h)
  next_fin(SCon{'{', x}, stack, False{}, (Pull.SEv{Pull.EBeginObj{}}, Pull.Cur{x, Pull.FObj{Pull.SKey{},
    True{}} <> stack,
    False{}, False{}}),
    go_open_obj(x, stack, hs))

# a container closed in a slot a value may go lands there
law close_ok:
  for +ev: Pull.Ev
  for +x: String
  for +stack: List<&2, Pull.Frame>
  for h: {Pull.expect.val.go(stack) == True{} : Bool}
  {Pull.next.go(4n, x, Pull.close.out(ev, stack, Pull.GNext{})) == Pull.Fin{(Pull.SEv{ev}, M4.aft(x,
      stack))} : Pull.Out}

def close_ok(ev, x, stack, h):
  match stack:
    case Nil{}:
      go_rest(3n, x, Pull.SEv{ev}, [], Pull.GNext{}, True{}, False{})
    case Pull.FArr{Pull.SVal{}, _} <> +oo:
      go_rest(3n, x, Pull.SEv{ev}, Pull.FArr{Pull.SCom{}, False{}} <> oo, Pull.GNext{}, False{}, False{})
    case Pull.FObj{Pull.SVal{}, _} <> +oo:
      go_rest(3n, x, Pull.SEv{ev}, Pull.FObj{Pull.SCom{}, False{}} <> oo, Pull.GNext{}, False{}, False{})
    case Pull.FArr{Pull.SCom{}, fr} <> oo:
      M6.no({Pull.next.go(4n, x, Pull.close.out(ev, Pull.FArr{Pull.SCom{}, fr} <> oo, Pull.GNext{}))
        == Pull.Fin{(Pull.SEv{ev}, M4.aft(x, Pull.FArr{Pull.SCom{}, fr} <> oo))} : Pull.Out}, h)
    case Pull.FArr{Pull.SKey{}, fr} <> oo:
      M6.no({Pull.next.go(4n, x, Pull.close.out(ev, Pull.FArr{Pull.SKey{}, fr} <> oo, Pull.GNext{}))
        == Pull.Fin{(Pull.SEv{ev}, M4.aft(x, Pull.FArr{Pull.SKey{}, fr} <> oo))} : Pull.Out}, h)
    case Pull.FArr{Pull.SCol{}, fr} <> oo:
      M6.no({Pull.next.go(4n, x, Pull.close.out(ev, Pull.FArr{Pull.SCol{}, fr} <> oo, Pull.GNext{}))
        == Pull.Fin{(Pull.SEv{ev}, M4.aft(x, Pull.FArr{Pull.SCol{}, fr} <> oo))} : Pull.Out}, h)
    case Pull.FObj{Pull.SCom{}, fr} <> oo:
      M6.no({Pull.next.go(4n, x, Pull.close.out(ev, Pull.FObj{Pull.SCom{}, fr} <> oo, Pull.GNext{}))
        == Pull.Fin{(Pull.SEv{ev}, M4.aft(x, Pull.FObj{Pull.SCom{}, fr} <> oo))} : Pull.Out}, h)
    case Pull.FObj{Pull.SKey{}, fr} <> oo:
      M6.no({Pull.next.go(4n, x, Pull.close.out(ev, Pull.FObj{Pull.SKey{}, fr} <> oo, Pull.GNext{}))
        == Pull.Fin{(Pull.SEv{ev}, M4.aft(x, Pull.FObj{Pull.SKey{}, fr} <> oo))} : Pull.Out}, h)
    case Pull.FObj{Pull.SCol{}, fr} <> oo:
      M6.no({Pull.next.go(4n, x, Pull.close.out(ev, Pull.FObj{Pull.SCol{}, fr} <> oo, Pull.GNext{}))
        == Pull.Fin{(Pull.SEv{ev}, M4.aft(x, Pull.FObj{Pull.SCol{}, fr} <> oo))} : Pull.Out}, h)

# `]` after an element closes the array
law next_carr:
  for +x: String
  for +fr: Bool
  for +stack: List<&2, Pull.Frame>
  for h: {Pull.expect.val.go(stack) == True{} : Bool}
  {Ezjson.next(Pull.Cur{SCon{']', x}, Pull.FArr{Pull.SCom{}, fr} <> stack, False{}, False{}})
    == (Pull.EEndArr{}, M4.aft(x, stack)) : (Pull.Ev & Pull.Cur)}

def next_carr(x, fr, stack, h):
  next_fin(SCon{']', x}, Pull.FArr{Pull.SCom{}, fr} <> stack, False{}, (Pull.SEv{Pull.EEndArr{}}, M4.aft(x, stack)),
    close_ok(Pull.EEndArr{}, x, stack, h))

# `]` of an empty array closes it
law next_carr0:
  for +x: String
  for +stack: List<&2, Pull.Frame>
  for h: {Pull.expect.val.go(stack) == True{} : Bool}
  {Ezjson.next(Pull.Cur{SCon{']', x}, Pull.FArr{Pull.SVal{}, True{}} <> stack, False{}, False{}})
    == (Pull.EEndArr{}, M4.aft(x, stack)) : (Pull.Ev & Pull.Cur)}

def next_carr0(x, stack, h):
  next_fin(SCon{']', x}, Pull.FArr{Pull.SVal{}, True{}} <> stack, False{}, (Pull.SEv{Pull.EEndArr{}}, M4.aft(x, stack)),
    close_ok(Pull.EEndArr{}, x, stack, h))

# `}` after a member closes the object
law next_cobj:
  for +x: String
  for +fr: Bool
  for +stack: List<&2, Pull.Frame>
  for h: {Pull.expect.val.go(stack) == True{} : Bool}
  {Ezjson.next(Pull.Cur{SCon{'}', x}, Pull.FObj{Pull.SCom{}, fr} <> stack, False{}, False{}})
    == (Pull.EEndObj{}, M4.aft(x, stack)) : (Pull.Ev & Pull.Cur)}

def next_cobj(x, fr, stack, h):
  next_fin(SCon{'}', x}, Pull.FObj{Pull.SCom{}, fr} <> stack, False{}, (Pull.SEv{Pull.EEndObj{}}, M4.aft(x, stack)),
    close_ok(Pull.EEndObj{}, x, stack, h))

# `}` of an empty object closes it
law next_cobj0:
  for +x: String
  for +stack: List<&2, Pull.Frame>
  for h: {Pull.expect.val.go(stack) == True{} : Bool}
  {Ezjson.next(Pull.Cur{SCon{'}', x}, Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, False{}})
    == (Pull.EEndObj{}, M4.aft(x, stack)) : (Pull.Ev & Pull.Cur)}

def next_cobj0(x, stack, h):
  next_fin(SCon{'}', x}, Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, (Pull.SEv{Pull.EEndObj{}}, M4.aft(x, stack)),
    close_ok(Pull.EEndObj{}, x, stack, h))

# whitespace, a comma and whitespace after an element: the next element's slot
law next_comma_arr:
  for +w1: String
  for +w2: String
  for +x: String
  for +fr: Bool
  for +stack: List<&2, Pull.Frame>
  for h1: {D1.all_ws(w1) == True{} : Bool}
  for h2: {D1.all_ws(w2) == True{} : Bool}
  {Ezjson.next(Pull.Cur{w1 ++ SCon{',', w2 ++ x}, Pull.FArr{Pull.SCom{}, fr} <> stack, False{}, False{}})
    == Ezjson.next(Pull.Cur{x, Pull.FArr{Pull.SVal{}, False{}} <> stack, False{}, False{}}) : (Pull.Ev & Pull.Cur)}

def next_comma_arr(w1, w2, x, fr, stack, h1, h2):
  Equal.trans((Pull.Ev & Pull.Cur),
    Ezjson.next(Pull.Cur{w1 ++ SCon{',', w2 ++ x}, Pull.FArr{Pull.SCom{}, fr} <> stack, False{}, False{}}),
    Ezjson.next(Pull.Cur{SCon{',', w2 ++ x}, Pull.FArr{Pull.SCom{}, fr} <> stack, False{}, False{}}),
    Ezjson.next(Pull.Cur{x, Pull.FArr{Pull.SVal{}, False{}} <> stack, False{}, False{}}),
    next_ws(w1, SCon{',', w2 ++ x}, Pull.FArr{Pull.SCom{}, fr} <> stack, False{}, h1),
    go_next(SCon{',', w2 ++ x}, Pull.FArr{Pull.SCom{}, fr} <> stack, False{}, x,
      Pull.FArr{Pull.SVal{}, False{}} <> stack, False{},
      go_wsd(3n, w2, x, Pull.FArr{Pull.SVal{}, False{}} <> stack, Pull.GNext{}, False{}, h2)))

# whitespace, a comma and whitespace after a member: the next member's name
law next_comma_obj:
  for +w1: String
  for +w2: String
  for +x: String
  for +fr: Bool
  for +stack: List<&2, Pull.Frame>
  for h1: {D1.all_ws(w1) == True{} : Bool}
  for h2: {D1.all_ws(w2) == True{} : Bool}
  {Ezjson.next(Pull.Cur{w1 ++ SCon{',', w2 ++ x}, Pull.FObj{Pull.SCom{}, fr} <> stack, False{}, False{}})
    == Ezjson.next(Pull.Cur{x, Pull.FObj{Pull.SKey{}, False{}} <> stack, False{}, False{}}) : (Pull.Ev & Pull.Cur)}

def next_comma_obj(w1, w2, x, fr, stack, h1, h2):
  Equal.trans((Pull.Ev & Pull.Cur),
    Ezjson.next(Pull.Cur{w1 ++ SCon{',', w2 ++ x}, Pull.FObj{Pull.SCom{}, fr} <> stack, False{}, False{}}),
    Ezjson.next(Pull.Cur{SCon{',', w2 ++ x}, Pull.FObj{Pull.SCom{}, fr} <> stack, False{}, False{}}),
    Ezjson.next(Pull.Cur{x, Pull.FObj{Pull.SKey{}, False{}} <> stack, False{}, False{}}),
    next_ws(w1, SCon{',', w2 ++ x}, Pull.FObj{Pull.SCom{}, fr} <> stack, False{}, h1),
    go_next(SCon{',', w2 ++ x}, Pull.FObj{Pull.SCom{}, fr} <> stack, False{}, x,
      Pull.FObj{Pull.SKey{}, False{}} <> stack, False{},
      go_wsd(3n, w2, x, Pull.FObj{Pull.SKey{}, False{}} <> stack, Pull.GNext{}, False{}, h2)))

# whitespace, a colon and whitespace after a name: the member's value's slot
law next_colon:
  for +w1: String
  for +w2: String
  for +x: String
  for +fr: Bool
  for +stack: List<&2, Pull.Frame>
  for h1: {D1.all_ws(w1) == True{} : Bool}
  for h2: {D1.all_ws(w2) == True{} : Bool}
  {Ezjson.next(Pull.Cur{w1 ++ SCon{':', w2 ++ x}, Pull.FObj{Pull.SCol{}, fr} <> stack, False{}, False{}})
    == Ezjson.next(Pull.Cur{x, Pull.FObj{Pull.SVal{}, False{}} <> stack, False{}, False{}}) : (Pull.Ev & Pull.Cur)}

def next_colon(w1, w2, x, fr, stack, h1, h2):
  Equal.trans((Pull.Ev & Pull.Cur),
    Ezjson.next(Pull.Cur{w1 ++ SCon{':', w2 ++ x}, Pull.FObj{Pull.SCol{}, fr} <> stack, False{}, False{}}),
    Ezjson.next(Pull.Cur{SCon{':', w2 ++ x}, Pull.FObj{Pull.SCol{}, fr} <> stack, False{}, False{}}),
    Ezjson.next(Pull.Cur{x, Pull.FObj{Pull.SVal{}, False{}} <> stack, False{}, False{}}),
    next_ws(w1, SCon{':', w2 ++ x}, Pull.FObj{Pull.SCol{}, fr} <> stack, False{}, h1),
    go_next(SCon{':', w2 ++ x}, Pull.FObj{Pull.SCol{}, fr} <> stack, False{}, x,
      Pull.FObj{Pull.SVal{}, False{}} <> stack, False{},
      go_wsd(3n, w2, x, Pull.FObj{Pull.SVal{}, False{}} <> stack, Pull.GNext{}, False{}, h2)))

# a count after one more for each character of a string
def addn(ws: String, nn: U32) -> U32:
  match ws:
    case SNil{}:
      nn
    case SCon{_, tl}:
      addn(tl, U32.add(nn, 1))

# what wrun says: the run on to the rest, and the span that has grown
def pwrun_ty(ws: String, tail: String, cut: String, buf: List<&2, Char>, nn: U32, num: V.Num) -> Type:
  ({Pull.word.run(ws ++ tail, Pull.WMore{buf, nn, num}) == Pull.word.run(tail, Pull.WMore{List.reverse.go(&2, Char,
    String.to_list(ws), buf), addn(ws, nn), M4.nfold(ws, num)}) : (String & Pull.Wst)}
    & ({M15.sdrop(cut, addn(ws, nn), U32.is_zero(addn(ws, nn))) == tail : String}
      & {Lex.tokens.rev(cut, addn(ws, nn), U32.is_zero(addn(ws, nn)), []) == List.reverse.go(&2, Char,
        String.to_list(ws), buf) : List<&2, Char>}))

# a word run over word characters, one character on, the rest given
law pwrun.cons:
  for +ch: Char
  for +tl: String
  for +tail: String
  for +cut: String
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for hc: {Lex.classify(ch) == Lex.COther{} : Lex.Class}
  for +h_d: {M15.sdrop(cut, nn, U32.is_zero(nn)) == SCon{ch, tl ++ tail} : String}
  for h_r: {Lex.tokens.rev(cut, nn, U32.is_zero(nn), []) == buf : List<&2, Char>}
  for h_s: {D1.short(cut) == True{} : Bool}
  for ih: {M15.sdrop(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1))) == tl ++ tail : String}
    -> {Lex.tokens.rev(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), []) == ch <> buf : List<&2, Char>}
    -> pwrun_ty(tl, tail, cut, ch <> buf, U32.add(nn, 1), V.num.ok.step(num, Char.to_u32(ch)))
  pwrun_ty(SCon{ch, tl}, tail, cut, buf, nn, num)

def pwrun.cons(ch, tl, tail, cut, buf, nn, num, hc, h_d, h_r, h_s, ih):
  +top = M2.pos_ne(cut, nn, 4294967295, U32.is_zero(nn), {==}, h_s, ch, tl ++ tail, h_d)
  +ed = M2.sdrop_grow(cut, nn, U32.is_zero(nn), {==}, top, ch, tl ++ tail, h_d)
  +er = Equal.trans(List<&2, Char>, Lex.tokens.rev(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), []),
    ch <> Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), ch <> buf,
    M2.rev_grow(cut, nn, U32.is_zero(nn), {==}, top, ch, tl ++ tail, h_d, []),
    Equal.cong(List<&2, Char>, List<&2, Char>, xx => ch <> xx, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), buf, h_r))

  dd = Equal.sym(Pull.Wst, Pull.word.decide(ch, Char.to_u32(ch), buf, nn, num),
    Pull.WMore{ch <> buf, U32.add(nn, 1), V.num.ok.step(num, Char.to_u32(ch))}, M4.decide_oth(ch, buf, nn, num, hc))
  %dd : ({Pull.word.run(tl ++ tail, _) == Pull.word.run(tail, Pull.WMore{List.reverse.go(&2, Char,
    String.to_list(tl), ch <> buf), addn(tl, U32.add(nn, 1)), M4.nfold(tl, V.num.ok.step(num, Char.to_u32(ch)))})
    : (String & Pull.Wst)}
    & ({M15.sdrop(cut, addn(tl, U32.add(nn, 1)), U32.is_zero(addn(tl, U32.add(nn, 1)))) == tail : String}
      & {Lex.tokens.rev(cut, addn(tl, U32.add(nn, 1)), U32.is_zero(addn(tl, U32.add(nn, 1))), [])
        == List.reverse.go(&2, Char, String.to_list(tl), ch <> buf) : List<&2, Char>}))
  ih(ed, er)

# a word run over word characters
law pwrun:
  for +ws: String
  for +tail: String
  for +cut: String
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for h_o: M17.others(String.to_list(ws))
  for h_d: {M15.sdrop(cut, nn, U32.is_zero(nn)) == ws ++ tail : String}
  for h_r: {Lex.tokens.rev(cut, nn, U32.is_zero(nn), []) == buf : List<&2, Char>}
  for +h_s: {D1.short(cut) == True{} : Bool}
  pwrun_ty(ws, tail, cut, buf, nn, num)

def pwrun(ws, tail, cut, buf, nn, num, h_o, h_d, h_r, h_s):
  match ws:
    case SNil{}:
      ({==}, (h_d, h_r))
    case SCon{+ch, +tl}:
      (hc, ht) = h_o
      pwrun.cons(ch, tl, tail, cut, buf, nn, num, hc, h_d, h_r, h_s,
        ed => er => pwrun(tl, tail, cut, ch <> buf, U32.add(nn, 1), V.num.ok.step(num, Char.to_u32(ch)), ht, ed, er,
          h_s))

# a scalar that lands where a value may go is that event, and the cursor
# moves on past it
law place_ok:
  for +ev: Pull.Ev
  for +rest: String
  for +stack: List<&2, Pull.Frame>
  for h_v: {Pull.expect.val.go(stack) == True{} : Bool}
  for +ff: Nat
  {Pull.next.go(1n+ff, "", Pull.place.val(ev, rest, stack, Pull.GNext{})) == Pull.Fin{(Pull.SEv{ev}, M4.aft(rest,
      stack))}
    : Pull.Out}

def place_ok(ev, rest, stack, h_v, ff):
  match stack:
    case Nil{}:
      {==}
    case Pull.FArr{Pull.SVal{}, _} <> _:
      {==}
    case Pull.FObj{Pull.SVal{}, _} <> _:
      {==}
    case Pull.FArr{Pull.SCom{}, fr} <> oo:
      M6.no({Pull.next.go(1n+ff, "", Pull.place.val(ev, rest, Pull.FArr{Pull.SCom{}, fr} <> oo, Pull.GNext{}))
        == Pull.Fin{(Pull.SEv{ev}, M4.aft(rest, Pull.FArr{Pull.SCom{}, fr} <> oo))} : Pull.Out}, h_v)
    case Pull.FArr{Pull.SKey{}, fr} <> oo:
      M6.no({Pull.next.go(1n+ff, "", Pull.place.val(ev, rest, Pull.FArr{Pull.SKey{}, fr} <> oo, Pull.GNext{}))
        == Pull.Fin{(Pull.SEv{ev}, M4.aft(rest, Pull.FArr{Pull.SKey{}, fr} <> oo))} : Pull.Out}, h_v)
    case Pull.FArr{Pull.SCol{}, fr} <> oo:
      M6.no({Pull.next.go(1n+ff, "", Pull.place.val(ev, rest, Pull.FArr{Pull.SCol{}, fr} <> oo, Pull.GNext{}))
        == Pull.Fin{(Pull.SEv{ev}, M4.aft(rest, Pull.FArr{Pull.SCol{}, fr} <> oo))} : Pull.Out}, h_v)
    case Pull.FObj{Pull.SCom{}, fr} <> oo:
      M6.no({Pull.next.go(1n+ff, "", Pull.place.val(ev, rest, Pull.FObj{Pull.SCom{}, fr} <> oo, Pull.GNext{}))
        == Pull.Fin{(Pull.SEv{ev}, M4.aft(rest, Pull.FObj{Pull.SCom{}, fr} <> oo))} : Pull.Out}, h_v)
    case Pull.FObj{Pull.SKey{}, fr} <> oo:
      M6.no({Pull.next.go(1n+ff, "", Pull.place.val(ev, rest, Pull.FObj{Pull.SKey{}, fr} <> oo, Pull.GNext{}))
        == Pull.Fin{(Pull.SEv{ev}, M4.aft(rest, Pull.FObj{Pull.SKey{}, fr} <> oo))} : Pull.Out}, h_v)
    case Pull.FObj{Pull.SCol{}, fr} <> oo:
      M6.no({Pull.next.go(1n+ff, "", Pull.place.val(ev, rest, Pull.FObj{Pull.SCol{}, fr} <> oo, Pull.GNext{}))
        == Pull.Fin{(Pull.SEv{ev}, M4.aft(rest, Pull.FObj{Pull.SCol{}, fr} <> oo))} : Pull.Out}, h_v)

# a word's end at the text's end, once its kind is named
law burst_eof:
  for +ff: Nat
  for +stack: List<&2, Pull.Frame>
  for +raw: String
  for +nn: U32
  for +atom: Pull.Atom
  for h_k: {M4.is_abad(atom) == False{} : Bool}
  for h_v: {Pull.expect.val.go(stack) == True{} : Bool}
  {Pull.next.go(1n+ff, "", Pull.word.eof.place(atom, raw, nn, stack, Pull.GNext{}))
    == Pull.Fin{(Pull.SEv{M4.aev(atom, raw, nn)}, M4.aft("", stack))} : Pull.Out}

def burst_eof(ff, stack, raw, nn, atom, h_k, h_v):
  match atom:
    case Pull.ANull{}:
      place_ok(Pull.ENull{}, "", stack, h_v, ff)
    case Pull.ATrue{}:
      place_ok(Pull.EBool{True{}}, "", stack, h_v, ff)
    case Pull.AFalse{}:
      place_ok(Pull.EBool{False{}}, "", stack, h_v, ff)
    case Pull.ANum{}:
      place_ok(Pull.ENum{raw, nn}, "", stack, h_v, ff)
    case Pull.ABad{}:
      Empty.absurd({Pull.next.go(1n+ff, "", Pull.word.eof.place(Pull.ABad{}, raw, nn, stack, Pull.GNext{}))
        == Pull.Fin{(Pull.SEv{M4.aev(Pull.ABad{}, raw, nn)}, M4.aft("", stack))} : Pull.Out}, M1.true_false(h_k))

# a word's end at a delimiter, once its kind is named
law burst_stop:
  for +ff: Nat
  for +stack: List<&2, Pull.Frame>
  for +ch: Char
  for +rr: String
  for +raw: String
  for +nn: U32
  for +atom: Pull.Atom
  for h_k: {M4.is_abad(atom) == False{} : Bool}
  for h_v: {Pull.expect.val.go(stack) == True{} : Bool}
  {Pull.next.go(1n+ff, "", Pull.word.burst.atom(rr, ch, raw, nn, stack, Pull.GNext{}, atom))
    == Pull.Fin{(Pull.SEv{M4.aev(atom, raw, nn)}, M4.aft(SCon{ch, rr}, stack))} : Pull.Out}

def burst_stop(ff, stack, ch, rr, raw, nn, atom, h_k, h_v):
  match atom:
    case Pull.ANull{}:
      place_ok(Pull.ENull{}, SCon{ch, rr}, stack, h_v, ff)
    case Pull.ATrue{}:
      place_ok(Pull.EBool{True{}}, SCon{ch, rr}, stack, h_v, ff)
    case Pull.AFalse{}:
      place_ok(Pull.EBool{False{}}, SCon{ch, rr}, stack, h_v, ff)
    case Pull.ANum{}:
      place_ok(Pull.ENum{raw, nn}, SCon{ch, rr}, stack, h_v, ff)
    case Pull.ABad{}:
      Empty.absurd({Pull.next.go(1n+ff, "", Pull.word.burst.atom(rr, ch, raw, nn, stack, Pull.GNext{}, Pull.ABad{}))
        == Pull.Fin{(Pull.SEv{M4.aev(Pull.ABad{}, raw, nn)}, M4.aft(SCon{ch, rr}, stack))} : Pull.Out},
            M1.true_false(h_k))

# a word's end: the word lands as its kind's event, and the cursor moves on
# to its delimiter
law burst_fin:
  for +ff: Nat
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for h_k: {M4.is_abad(Pull.word.kind(Lex.text(buf), nn, num)) == False{} : Bool}
  for h_t: {M6.stops(tail) == True{} : Bool}
  for h_v: {Pull.expect.val.go(stack) == True{} : Bool}
  {Pull.next.go(1n+ff, "", Pull.word.burst.at(Pull.word.run(tail, Pull.WMore{buf, nn, num}), stack, Pull.GNext{}))
    == Pull.Fin{(Pull.SEv{M4.aev(Pull.word.kind(Lex.text(buf), nn, num), Lex.text(buf), nn)}, M4.aft(tail, stack))}
    : Pull.Out}

def burst_fin(ff, tail, stack, buf, nn, num, h_k, h_t, h_v):
  match tail:
    case SNil{}:
      burst_eof(ff, stack, Lex.text(buf), nn, Pull.word.kind(Lex.text(buf), nn, num), h_k, h_v)
    case SCon{+ch, +rr}:
      ds = Equal.sym(Pull.Wst, Pull.word.decide(ch, Char.to_u32(ch), buf, nn, num), Pull.WStop{buf, nn, num, ch},
        M4.decide_stop(ch, buf, nn, num, M14.not_true(M6.is_other(Lex.classify(ch)), h_t)))
      %ds : {Pull.next.go(1n+ff, "", Pull.word.burst.at(Pull.word.run(rr, _), stack, Pull.GNext{}))
        == Pull.Fin{(Pull.SEv{M4.aev(Pull.word.kind(Lex.text(buf), nn, num), Lex.text(buf), nn)}, M4.aft(SCon{ch, rr},
          stack))} : Pull.Out}
      rs = Equal.sym((String & Pull.Wst), Pull.word.run(rr, Pull.WStop{buf, nn, num, ch}),
        (rr, Pull.WStop{buf, nn, num, ch}), M4.run_stopped(rr, buf, nn, num, ch))
      %rs : {Pull.next.go(1n+ff, "", Pull.word.burst.at(_, stack, Pull.GNext{}))
        == Pull.Fin{(Pull.SEv{M4.aev(Pull.word.kind(Lex.text(buf), nn, num), Lex.text(buf), nn)}, M4.aft(SCon{ch, rr},
          stack))} : Pull.Out}
      burst_stop(ff, stack, ch, rr, Lex.text(buf), nn, Pull.word.kind(Lex.text(buf), nn, num), h_k, h_v)

# a word that is none of the literal names: lit_or_num is number
law lit_num.e:
  for +ww: String
  for e1: {String.eq(ww, "null") == False{} : Bool}
  for e2: {String.eq(ww, "true") == False{} : Bool}
  for e3: {String.eq(ww, "false") == False{} : Bool}
  {D1.lit_or_num(ww) == D1.number(String.to_list(ww)) : Bool}

def lit_num.e(ww, e1, e2, e3):
  s1 = Equal.sym(Bool, String.eq(ww, "null"), False{}, e1)
  s2 = Equal.sym(Bool, String.eq(ww, "true"), False{}, e2)
  s3 = Equal.sym(Bool, String.eq(ww, "false"), False{}, e3)
  %s1 : {Bool.or(_, Bool.or(String.eq(ww, "true"), Bool.or(String.eq(ww, "false"),
    D1.number(String.to_list(ww))))) == D1.number(String.to_list(ww)) : Bool}
  %s2 : {Bool.or(_, Bool.or(String.eq(ww, "false"), D1.number(String.to_list(ww)))) == D1.number(String.to_list(ww))
    : Bool}
  %s3 : {Bool.or(_, D1.number(String.to_list(ww))) == D1.number(String.to_list(ww)) : Bool}
  {==}

# a word that is none of the literal names is a number
law lit_num:
  for +ww: String
  for e1: {String.eq(ww, "null") == False{} : Bool}
  for e2: {String.eq(ww, "true") == False{} : Bool}
  for e3: {String.eq(ww, "false") == False{} : Bool}
  for h_w: {D1.lit_or_num(ww) == True{} : Bool}
  {D1.number(String.to_list(ww)) == True{} : Bool}

def lit_num(ww, e1, e2, e3, h_w):
  Equal.trans(Bool, D1.number(String.to_list(ww)), D1.lit_or_num(ww), True{},
    Equal.sym(Bool, D1.lit_or_num(ww), D1.number(String.to_list(ww)), lit_num.e(ww, e1, e2, e3)), h_w)

# what wk_ev says: the word's kind is one, and its event is the value's
def wk_ty(ww: String, num: V.Num, nn: U32) -> Type:
  ({M4.is_abad(M4.wk(ww, num)) == False{} : Bool}
    & {D1.events(L2.g.word(ww)) == [D1.view(M4.aev(M4.wk(ww, num), ww, nn))] : List<&2, D1.Evt>})

# a literal name's or a number's kind and event, with the literal tests named
law wk_ev.at:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for +ww: String
  for +num: V.Num
  for +nn: U32
  for +e1: {String.eq(ww, "null") == b1 : Bool}
  for +e2: {String.eq(ww, "true") == b2 : Bool}
  for +e3: {String.eq(ww, "false") == b3 : Bool}
  for h_w: {D1.lit_or_num(ww) == True{} : Bool}
  for h_num: {V.num.ok.done(num) == D1.number(String.to_list(ww)) : Bool}
  for h_tk: {D1.take(ww, U32.to_nat(nn)) == ww : String}
  wk_ty(ww, num, nn)

def wk_ev.at(b1, b2, b3, ww, num, nn, e1, e2, e3, h_w, h_num, h_tk):
  match b1:
    case True{}:
      ek = Equal.sym(String, ww, "null", M9.str_eq_sound(ww, "null", e1))
      %ek : wk_ty(_, num, nn)
      ({==}, {==})
    case False{}:
      match b2:
        case True{}:
          ek = Equal.sym(String, ww, "true", M9.str_eq_sound(ww, "true", e2))
          %ek : wk_ty(_, num, nn)
          ({==}, {==})
        case False{}:
          match b3:
            case True{}:
              ek = Equal.sym(String, ww, "false", M9.str_eq_sound(ww, "false", e3))
              %ek : wk_ty(_, num, nn)
              ({==}, {==})
            case False{}:
              +hn = lit_num(ww, e1, e2, e3, h_w)
              s1 = Equal.sym(Bool, String.eq(ww, "null"), False{}, e1)
              s2 = Equal.sym(Bool, String.eq(ww, "true"), False{}, e2)
              s3 = Equal.sym(Bool, String.eq(ww, "false"), False{}, e3)
              %s1 : ({M4.is_abad(Pull.word.kind.go(num, _, String.eq(ww, "true"), String.eq(ww, "false"))) == False{}
                : Bool}
                & {D1.events(Bool.pick(V.Json, _, V.JNull{}, Bool.pick(V.Json, String.eq(ww, "true"),
                  V.JBool{True{}}, Bool.pick(V.Json, String.eq(ww, "false"), V.JBool{False{}}, V.JNum{ww}))))
                  == [D1.view(M4.aev(Pull.word.kind.go(num, _, String.eq(ww, "true"), String.eq(ww, "false")), ww,
                    nn))] : List<&2, D1.Evt>})
              %s2 : ({M4.is_abad(Pull.word.kind.go(num, False{}, _, String.eq(ww, "false"))) == False{} : Bool}
                & {D1.events(Bool.pick(V.Json, _, V.JBool{True{}}, Bool.pick(V.Json, String.eq(ww, "false"),
                  V.JBool{False{}}, V.JNum{ww})))
                  == [D1.view(M4.aev(Pull.word.kind.go(num, False{}, _, String.eq(ww, "false")), ww, nn))]
                  : List<&2, D1.Evt>})
              %s3 : ({M4.is_abad(Pull.word.kind.go(num, False{}, False{}, _)) == False{} : Bool}
                & {D1.events(Bool.pick(V.Json, _, V.JBool{False{}}, V.JNum{ww}))
                  == [D1.view(M4.aev(Pull.word.kind.go(num, False{}, False{}, _), ww, nn))] : List<&2, D1.Evt>})
              en = Equal.sym(Bool, V.num.ok.done(num), True{}, Equal.trans(Bool, V.num.ok.done(num),
                D1.number(String.to_list(ww)), True{}, h_num, hn))
              %en : ({M4.is_abad(Pull.word.kind.num(_)) == False{} : Bool}
                & {[D1.VNum{ww}] == [D1.view(M4.aev(Pull.word.kind.num(_), ww, nn))] : List<&2, D1.Evt>})
              ({==}, Equal.cong(String, List<&2, D1.Evt>, xx => [D1.VNum{xx}], ww, D1.take(ww, U32.to_nat(nn)),
                Equal.sym(String, D1.take(ww, U32.to_nat(nn)), ww, h_tk)))

# a literal name's or a number's kind and event
law wk_ev:
  for +ww: String
  for +num: V.Num
  for +nn: U32
  for h_w: {D1.lit_or_num(ww) == True{} : Bool}
  for h_num: {V.num.ok.done(num) == D1.number(String.to_list(ww)) : Bool}
  for h_tk: {D1.take(ww, U32.to_nat(nn)) == ww : String}
  wk_ty(ww, num, nn)

def wk_ev(ww, num, nn, h_w, h_num, h_tk):
  wk_ev.at(String.eq(ww, "null"), String.eq(ww, "true"), String.eq(ww, "false"), ww, num, nn, {==}, {==}, {==}, h_w,
    h_num, h_tk)

# a word's buffer, its first character then the rest reversed on, reads back as the word
law wtext:
  for +ch: Char
  for +tl: String
  {Lex.text(List.reverse.go(&2, Char, String.to_list(tl), [ch])) == SCon{ch, tl} : String}

def wtext(ch, tl):
  Equal.trans(String, Lex.text(List.reverse.go(&2, Char, String.to_list(tl), [ch])),
    SCon{ch, String.from_list(String.to_list(tl)) ++ ""}, SCon{ch, tl},
    M6.text_revgo(String.to_list(tl), [ch], ""),
    Equal.cong(String, String, xx => SCon{ch, xx}, String.from_list(String.to_list(tl)) ++ "", tl,
      Equal.trans(String, String.from_list(String.to_list(tl)) ++ "", String.from_list(String.to_list(tl)), tl,
        M6.append_nil(String.from_list(String.to_list(tl))), M6.from_to(tl))))

# a finished step on a word's event is that event
law use_aev:
  for +atom: Pull.Atom
  for +raw: String
  for +nn: U32
  for cur: Pull.Cur
  for h_k: {M4.is_abad(atom) == False{} : Bool}
  {Pull.next.use((Pull.SEv{M4.aev(atom, raw, nn)}, cur)) == (M4.aev(atom, raw, nn), cur) : (Pull.Ev & Pull.Cur)}

def use_aev(atom, raw, nn, cur, h_k):
  match atom:
    case Pull.ANull{}:
      {==}
    case Pull.ATrue{}:
      {==}
    case Pull.AFalse{}:
      {==}
    case Pull.ANum{}:
      {==}
    case Pull.ABad{}:
      Empty.absurd({Pull.next.use((Pull.SEv{M4.aev(Pull.ABad{}, raw, nn)}, cur)) == (M4.aev(Pull.ABad{}, raw, nn), cur)
        : (Pull.Ev & Pull.Cur)}, M1.true_false(h_k))

# a literal name's or a number's word characters
law lit_others.at:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for +ww: String
  for +e1: {String.eq(ww, "null") == b1 : Bool}
  for +e2: {String.eq(ww, "true") == b2 : Bool}
  for +e3: {String.eq(ww, "false") == b3 : Bool}
  for h_w: {D1.lit_or_num(ww) == True{} : Bool}
  M17.others(String.to_list(ww))

def lit_others.at(b1, b2, b3, ww, e1, e2, e3, h_w):
  match b1:
    case True{}:
      ek = Equal.sym(String, ww, "null", M9.str_eq_sound(ww, "null", e1))
      %ek : M17.others(String.to_list(_))
      ({==}, ({==}, ({==}, ({==}, Unit{}))))
    case False{}:
      match b2:
        case True{}:
          ek = Equal.sym(String, ww, "true", M9.str_eq_sound(ww, "true", e2))
          %ek : M17.others(String.to_list(_))
          ({==}, ({==}, ({==}, ({==}, Unit{}))))
        case False{}:
          match b3:
            case True{}:
              ek = Equal.sym(String, ww, "false", M9.str_eq_sound(ww, "false", e3))
              %ek : M17.others(String.to_list(_))
              ({==}, ({==}, ({==}, ({==}, ({==}, Unit{})))))
            case False{}:
              M9.oth_number(String.to_list(ww), lit_num(ww, e1, e2, e3, h_w))

# a literal name's or a number's word characters
law lit_others:
  for +ww: String
  for h_w: {D1.lit_or_num(ww) == True{} : Bool}
  M17.others(String.to_list(ww))

def lit_others(ww, h_w):
  lit_others.at(String.eq(ww, "null"), String.eq(ww, "true"), String.eq(ww, "false"), ww, {==}, {==}, {==}, h_w)

# wk_ev's first half
law wk_fst:
  for ww: String
  for num: V.Num
  for nn: U32
  for h: wk_ty(ww, num, nn)
  {M4.is_abad(M4.wk(ww, num)) == False{} : Bool}

def wk_fst(_ww, _num, _nn, h):
  (aa, _bb) = h
  aa

# wk_ev's second half
law wk_snd:
  for ww: String
  for num: V.Num
  for nn: U32
  for h: wk_ty(ww, num, nn)
  {D1.events(L2.g.word(ww)) == [D1.view(M4.aev(M4.wk(ww, num), ww, nn))] : List<&2, D1.Evt>}

def wk_snd(_ww, _num, _nn, h):
  (_aa, bb) = h
  bb

# a word's first step is the burst over the whole rest, whatever it is
law go_mword:
  for +ff: Nat
  for +txt: String
  for buf: List<&2, Char>
  for nn: U32
  for num: V.Num
  for stack: List<&2, Pull.Frame>
  for goal: Pull.Goal
  for done: Bool
  for bad: Bool
  {Pull.next.go(1n+ff, txt, Pull.S{Pull.MWord{buf, nn, num}, stack, goal, done, bad})
    == Pull.next.go(ff, "", Pull.word.burst(txt, buf, nn, num, stack, goal, bad)) : Pull.Out}

def go_mword(_ff, txt, _buf, _nn, _num, _stack, _goal, _done, _bad):
  match txt:
    case SNil{}:
      {==}
    case SCon{_, _}:
      {==}

law go_word.b:
  for +ch: Char
  for +tl: String
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +h_v: {Pull.expect.val.go(stack) == True{} : Bool}
  for e_run: {Pull.word.run(tl ++ tail, Pull.WMore{[ch], 1, V.num.ok.step(V.NStart{}, Char.to_u32(ch))})
    == Pull.word.run(tail, Pull.WMore{List.reverse.go(&2, Char, String.to_list(tl), [ch]), addn(tl, 1),
      M4.nfold(tl, V.num.ok.step(V.NStart{}, Char.to_u32(ch)))}) : (String & Pull.Wst)}
  for hk: {M4.is_abad(Pull.word.kind(Lex.text(List.reverse.go(&2, Char, String.to_list(tl), [ch])), addn(tl, 1),
    M4.nfold(tl, V.num.ok.step(V.NStart{}, Char.to_u32(ch))))) == False{} : Bool}
  for h_t: {M6.stops(tail) == True{} : Bool}
  {Pull.next.go(3n, "", Pull.word.burst(tl ++ tail, [ch], 1, V.num.ok.step(V.NStart{}, Char.to_u32(ch)), stack,
    Pull.GNext{}, False{}))
    == Pull.Fin{(Pull.SEv{M4.aev(Pull.word.kind(Lex.text(List.reverse.go(&2, Char, String.to_list(tl), [ch])),
      addn(tl, 1), M4.nfold(tl, V.num.ok.step(V.NStart{}, Char.to_u32(ch)))),
      Lex.text(List.reverse.go(&2, Char, String.to_list(tl), [ch])), addn(tl, 1))}, M4.aft(tail, stack))} : Pull.Out}

def go_word.b(ch, tl, tail, stack, h_v, e_run, hk, h_t):
  +bf = List.reverse.go(&2, Char, String.to_list(tl), [ch])
  +nf = addn(tl, 1)
  +mf = M4.nfold(tl, V.num.ok.step(V.NStart{}, Char.to_u32(ch)))
  ers = Equal.sym((String & Pull.Wst), Pull.word.run(tl ++ tail, Pull.WMore{[ch], 1, V.num.ok.step(V.NStart{},
    Char.to_u32(ch))}), Pull.word.run(tail, Pull.WMore{bf, nf, mf}), e_run)
  %ers : {Pull.next.go(3n, "", Pull.word.burst.at(_, stack,
    Pull.GNext{})) == Pull.Fin{(Pull.SEv{M4.aev(Pull.word.kind(Lex.text(bf), nf, mf), Lex.text(bf), nf)}, M4.aft(tail,
    stack))} : Pull.Out}
  burst_fin(2n, tail, stack, bf, nf, mf, hk, h_t, h_v)

# the first budget's walk over a word and its delimiter
law go_word:
  for +ch: Char
  for +tl: String
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for hc: {Lex.classify(ch) == Lex.COther{} : Lex.Class}
  for +h_v: {Pull.expect.val.go(stack) == True{} : Bool}
  for e_run: {Pull.word.run(tl ++ tail, Pull.WMore{[ch], 1, V.num.ok.step(V.NStart{}, Char.to_u32(ch))})
    == Pull.word.run(tail, Pull.WMore{List.reverse.go(&2, Char, String.to_list(tl), [ch]), addn(tl, 1),
      M4.nfold(tl, V.num.ok.step(V.NStart{}, Char.to_u32(ch)))}) : (String & Pull.Wst)}
  for hk: {M4.is_abad(Pull.word.kind(Lex.text(List.reverse.go(&2, Char, String.to_list(tl), [ch])), addn(tl, 1),
    M4.nfold(tl, V.num.ok.step(V.NStart{}, Char.to_u32(ch))))) == False{} : Bool}
  for h_t: {M6.stops(tail) == True{} : Bool}
  {Pull.next.go(4n, SCon{ch, tl ++ tail}, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, False{}, False{}})
    == Pull.Fin{(Pull.SEv{M4.aev(Pull.word.kind(Lex.text(List.reverse.go(&2, Char, String.to_list(tl), [ch])),
      addn(tl, 1), M4.nfold(tl, V.num.ok.step(V.NStart{}, Char.to_u32(ch)))),
      Lex.text(List.reverse.go(&2, Char, String.to_list(tl), [ch])), addn(tl, 1))}, M4.aft(tail, stack))} : Pull.Out}

def go_word(ch, tl, tail, stack, hc, h_v, e_run, hk, h_t):
  +bf = List.reverse.go(&2, Char, String.to_list(tl), [ch])
  +nf = addn(tl, 1)
  +mf = M4.nfold(tl, V.num.ok.step(V.NStart{}, Char.to_u32(ch)))
  hcs = Equal.sym(Lex.Class, Lex.classify(ch), Lex.COther{}, hc)
  %hcs : {Pull.next.go(4n, tl ++ tail, Pull.look.plan(ch, stack, Pull.GNext{}, False{},
    _)) == Pull.Fin{(Pull.SEv{M4.aev(Pull.word.kind(Lex.text(bf), nf, mf), Lex.text(bf), nf)}, M4.aft(tail,
    stack))} : Pull.Out}
  hvs = Equal.sym(Bool, Pull.expect.val.go(stack), True{}, h_v)
  %hvs : {Pull.next.go(4n, tl ++ tail, Pull.look.word(ch, stack, Pull.GNext{}, False{},
    _)) == Pull.Fin{(Pull.SEv{M4.aev(Pull.word.kind(Lex.text(bf), nf, mf), Lex.text(bf), nf)}, M4.aft(tail,
    stack))} : Pull.Out}
  +m0 = V.num.ok.step(V.NStart{}, Char.to_u32(ch))
  Equal.trans(Pull.Out, Pull.next.go(4n, tl ++ tail, Pull.S{Pull.MWord{[ch], 1, m0}, stack, Pull.GNext{}, False{},
    False{}}), Pull.next.go(3n, "", Pull.word.burst(tl ++ tail, [ch], 1, m0, stack, Pull.GNext{}, False{})),
      Pull.Fin{(Pull.SEv{M4.aev(Pull.word.kind(Lex.text(bf), nf, mf), Lex.text(bf), nf)}, M4.aft(tail, stack))},
    go_mword(3n, tl ++ tail, [ch], 1, m0, stack, Pull.GNext{}, False{}, False{}),
    go_word.b(ch, tl, tail, stack, h_v, e_run, hk, h_t))

# a literal name or a number, once its first character and the run over the
# rest are in hand
law next_word.run:
  for +ch: Char
  for +tl: String
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for hc: {Lex.classify(ch) == Lex.COther{} : Lex.Class}
  for +h_w: {D1.lit_or_num(SCon{ch, tl}) == True{} : Bool}
  for +h_t: {M6.stops(tail) == True{} : Bool}
  for +h_v: {Pull.expect.val.go(stack) == True{} : Bool}
  for ww: pwrun_ty(tl, tail, SCon{ch, tl ++ tail}, [ch], 1, V.num.ok.step(V.NStart{}, Char.to_u32(ch)))
  for +c0: Pull.Cur
  for h_c: {Ezjson.next(c0) == Ezjson.next(Pull.Cur{SCon{ch, tl ++ tail}, stack, False{},
    False{}}) : (Pull.Ev & Pull.Cur)}
  strm(c0, D1.events(L2.g.word(SCon{ch, tl})), M4.aft(tail, stack))

def next_word.run(ch, tl, tail, stack, hc, h_w, h_t, h_v, ww, c0, h_c):
  (e_run, (_e_d, e_r)) = ww
  +m0 = V.num.ok.step(V.NStart{}, Char.to_u32(ch))
  +bf = List.reverse.go(&2, Char, String.to_list(tl), [ch])
  +nf = addn(tl, 1)
  +mf = M4.nfold(tl, m0)
  +wd = "" ++ SCon{ch, tl}
  +et = wtext(ch, tl)
  +htk = M4.tk_of(SCon{ch, tl ++ tail}, nf, bf, wd, e_r, et)
  +ek = Equal.trans(Pull.Atom, Pull.word.kind(Lex.text(bf), nf, mf), Pull.word.kind(wd, nf, mf), M4.wk(wd, mf),
    Equal.cong(String, Pull.Atom, xx => Pull.word.kind(xx, nf, mf), Lex.text(bf), wd, et), M4.kind_eq(wd, nf, mf, htk))
  +hnum = Equal.trans(Bool, V.num.ok.done(mf), V.num.ok(wd), D1.number(String.to_list(wd)),
    Equal.sym(Bool, V.num.ok(wd), V.num.ok.done(mf), M4.nok_fold(tl, m0)), L1.num_grammar(wd))

  +hk = Equal.trans(Bool, M4.is_abad(Pull.word.kind(Lex.text(bf), nf, mf)), M4.is_abad(M4.wk(wd, mf)), False{},
    Equal.cong(Pull.Atom, Bool, xx => M4.is_abad(xx), Pull.word.kind(Lex.text(bf), nf, mf), M4.wk(wd, mf), ek),
    wk_fst(wd, mf, nf, wk_ev(wd, mf, nf, h_w, hnum, htk)))
  +kk = Pull.word.kind(Lex.text(bf), nf, mf)
  main = Equal.trans((Pull.Ev & Pull.Cur), Ezjson.next(c0), Ezjson.next(Pull.Cur{SCon{ch, tl ++ tail}, stack, False{},
    False{}}), (M4.aev(kk, Lex.text(bf), nf), M4.aft(tail, stack)), h_c, Equal.trans((Pull.Ev & Pull.Cur),
    Ezjson.next(Pull.Cur{SCon{ch, tl ++ tail}, stack, False{}, False{}}), Pull.next.use((Pull.SEv{M4.aev(kk,
        Lex.text(bf),
      nf)},
    M4.aft(tail, stack))), (M4.aev(kk, Lex.text(bf), nf), M4.aft(tail, stack)),
    next_fin(SCon{ch, tl ++ tail}, stack, False{}, (Pull.SEv{M4.aev(kk, Lex.text(bf), nf)}, M4.aft(tail, stack)),
      go_word(ch, tl, tail, stack, hc, h_v, e_run, hk, h_t)),
    use_aev(kk, Lex.text(bf), nf, M4.aft(tail, stack), hk)))
  es = Equal.sym(List<&2, D1.Evt>, D1.events(L2.g.word(wd)), [D1.view(M4.aev(M4.wk(wd, mf), wd, nf))],
    wk_snd(wd, mf, nf, wk_ev(wd, mf, nf, h_w, hnum, htk)))
  %es : strm(c0, _, M4.aft(tail, stack))
  %ek : strm(c0, [D1.view(M4.aev(_, wd, nf))], M4.aft(tail, stack))
  %et : strm(c0, [D1.view(M4.aev(kk, _, nf))], M4.aft(tail, stack))
  strm_one(c0, M4.aev(kk, Lex.text(bf), nf), M4.aft(tail, stack), main)

# a literal name or a number, once its first character is in hand
law next_word.cons:
  for +ch: Char
  for +tl: String
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for ho: M17.others(String.to_list(SCon{ch, tl}))
  for +h_w: {D1.lit_or_num(SCon{ch, tl}) == True{} : Bool}
  for +h_t: {M6.stops(tail) == True{} : Bool}
  for +h_v: {Pull.expect.val.go(stack) == True{} : Bool}
  for +h_s: {D1.short(SCon{ch, tl ++ tail}) == True{} : Bool}
  for +c0: Pull.Cur
  for h_c: {Ezjson.next(c0) == Ezjson.next(Pull.Cur{SCon{ch, tl ++ tail}, stack, False{},
    False{}}) : (Pull.Ev & Pull.Cur)}
  strm(c0, D1.events(L2.g.word(SCon{ch, tl})), M4.aft(tail, stack))

def next_word.cons(ch, tl, tail, stack, ho, h_w, h_t, h_v, h_s, c0, h_c):
  (hc, ht) = ho
  next_word.run(ch, tl, tail, stack, hc, h_w, h_t, h_v, pwrun(tl, tail, SCon{ch, tl ++ tail}, [ch], 1,
    V.num.ok.step(V.NStart{}, Char.to_u32(ch)), ht, M2.sdrop_zero(tl ++ tail, tl ++ tail, {==}),
    M2.rev_zero(tl ++ tail, 0, [ch]), h_s), c0, h_c)

# the cursor reads a literal name or a number where a value may go, and moves
# on to the character after it
law next_word:
  for +ww: String
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +h_w: {D1.lit_or_num(ww) == True{} : Bool}
  for +h_t: {M6.stops(tail) == True{} : Bool}
  for +h_v: {Pull.expect.val.go(stack) == True{} : Bool}
  for +h_s: {D1.short(ww ++ tail) == True{} : Bool}
  for +c0: Pull.Cur
  for h_c: {Ezjson.next(c0) == Ezjson.next(Pull.Cur{ww ++ tail, stack, False{}, False{}}) : (Pull.Ev & Pull.Cur)}
  strm(c0, D1.events(L2.g.word(ww)), M4.aft(tail, stack))

def next_word(ww, tail, stack, h_w, h_t, h_v, h_s, c0, h_c):
  match ww:
    case SNil{}:
      M6.no(strm(c0, D1.events(L2.g.word("")), M4.aft(tail, stack)), h_w)
    case SCon{+ch, +tl}:
      next_word.cons(ch, tl, tail, stack, lit_others(SCon{ch, tl}, h_w), h_w, h_t, h_v, h_s, c0, h_c)

# laws/CursorEventsMatchParse.bend, strings

# a raw character is no quotation mark
law raw34:
  for +uu: U32
  for h: {D1.raw_char(Chr{uu}) == True{} : Bool}
  {U32.is_eq(uu, 34) == False{} : Bool}

def raw34(uu, h):
  M14.or_false_l(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_lt(uu, 32)),
    M14.not_true(Bool.or(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_lt(uu, 32))), h))

# a raw character is no reverse solidus
law raw92:
  for +uu: U32
  for h: {D1.raw_char(Chr{uu}) == True{} : Bool}
  {U32.is_eq(uu, 92) == False{} : Bool}

def raw92(uu, h):
  M14.or_false_l(U32.is_eq(uu, 92), U32.is_lt(uu, 32), M14.or_false_r(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92),
    U32.is_lt(uu, 32)), M14.not_true(Bool.or(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_lt(uu, 32))), h)))

# a raw character is no control
law rawlt:
  for +uu: U32
  for h: {D1.raw_char(Chr{uu}) == True{} : Bool}
  {U32.is_lt(uu, 32) == False{} : Bool}

def rawlt(uu, h):
  M14.or_false_r(U32.is_eq(uu, 92), U32.is_lt(uu, 32), M14.or_false_r(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92),
    U32.is_lt(uu, 32)), M14.not_true(Bool.or(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_lt(uu, 32))), h)))

# a raw character's class is no quotation mark's
law nq34:
  for +uu: U32
  for e34: {U32.is_eq(uu, 34) == False{} : Bool}
  for ecls: {Lex.classify(Chr{uu}) == Lex.CQuote{} : Lex.Class}
  Empty

def nq34(uu, e34, ecls):
  M6.false_true(Equal.trans(Bool, False{}, U32.is_eq(uu, 34), True{}, Equal.sym(Bool, U32.is_eq(uu, 34), False{}, e34),
    Equal.cong(U32, Bool, xx => U32.is_eq(xx, 34), uu, 34, M2.cls_quote(Chr{uu}, ecls))))

# a raw character's class is no reverse solidus'
law nb92:
  for +uu: U32
  for e92: {U32.is_eq(uu, 92) == False{} : Bool}
  for ecls: {Lex.classify(Chr{uu}) == Lex.CBack{} : Lex.Class}
  Empty

def nb92(uu, e92, ecls):
  M6.false_true(Equal.trans(Bool, False{}, U32.is_eq(uu, 92), True{}, Equal.sym(Bool, U32.is_eq(uu, 92), False{}, e92),
    Equal.cong(U32, Bool, xx => U32.is_eq(xx, 92), uu, 92, M2.cls_back(Chr{uu}, ecls))))

# a raw character stays in the string, by its class
law kind_go:
  for cls: Lex.Class
  for +uu: U32
  for ecls: {Lex.classify(Chr{uu}) == cls : Lex.Class}
  for e34: {U32.is_eq(uu, 34) == False{} : Bool}
  for e92: {U32.is_eq(uu, 92) == False{} : Bool}
  for ect: {U32.is_lt(uu, 32) == False{} : Bool}
  {Pull.span.kind(cls, U32.is_lt(uu, 32)) == Pull.KGo{} : Pull.Skind}

def kind_go(cls, uu, ecls, e34, e92, ect):
  match cls:
    case Lex.CQuote{}:
      Empty.absurd({Pull.span.kind(Lex.CQuote{}, U32.is_lt(uu, 32)) == Pull.KGo{} : Pull.Skind}, nq34(uu, e34, ecls))
    case Lex.CBack{}:
      Empty.absurd({Pull.span.kind(Lex.CBack{}, U32.is_lt(uu, 32)) == Pull.KGo{} : Pull.Skind}, nb92(uu, e92, ecls))
    case Lex.CPunct{tt}:
      ec = Equal.sym(Bool, U32.is_lt(uu, 32), False{}, ect)
      %ec : {Pull.span.kind(Lex.CPunct{tt}, _) == Pull.KGo{} : Pull.Skind}
      {==}
    case Lex.CSpace{}:
      ec = Equal.sym(Bool, U32.is_lt(uu, 32), False{}, ect)
      %ec : {Pull.span.kind(Lex.CSpace{}, _) == Pull.KGo{} : Pull.Skind}
      {==}
    case Lex.COther{}:
      ec = Equal.sym(Bool, U32.is_lt(uu, 32), False{}, ect)
      %ec : {Pull.span.kind(Lex.COther{}, _) == Pull.KGo{} : Pull.Skind}
      {==}

# a raw character stays in the string
law kind_raw:
  for +ch: Char
  for +h: {D1.raw_char(ch) == True{} : Bool}
  {Pull.span.kind.of(ch) == Pull.KGo{} : Pull.Skind}

def kind_raw(ch, h):
  match ch:
    case Chr{+uu}:
      kind_go(Lex.classify(Chr{uu}), uu, {==}, raw34(uu, h), raw92(uu, h), rawlt(uu, h))

# a raw character is copied, by its class
law copy_go:
  for cls: Lex.Class
  for +uu: U32
  for ecls: {Lex.classify(Chr{uu}) == cls : Lex.Class}
  for e34: {U32.is_eq(uu, 34) == False{} : Bool}
  for e92: {U32.is_eq(uu, 92) == False{} : Bool}
  for ect: {U32.is_lt(uu, 32) == False{} : Bool}
  for +tl: String
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  {Pull.copy.hit.go(Chr{uu}, tl, buf, stack, Pull.GNext{}, done, cls, U32.is_lt(uu, 32))
    == Pull.S{Pull.MCopy{Chr{uu} <> buf}, stack, Pull.GNext{}, done, False{}} : Pull.St}

def copy_go(cls, uu, ecls, e34, e92, ect, tl, buf, stack, done):
  match cls:
    case Lex.CQuote{}:
      Empty.absurd({Pull.copy.hit.go(Chr{uu}, tl, buf, stack, Pull.GNext{}, done, Lex.CQuote{}, U32.is_lt(uu, 32))
        == Pull.S{Pull.MCopy{Chr{uu} <> buf}, stack, Pull.GNext{}, done, False{}} : Pull.St}, nq34(uu, e34, ecls))
    case Lex.CBack{}:
      Empty.absurd({Pull.copy.hit.go(Chr{uu}, tl, buf, stack, Pull.GNext{}, done, Lex.CBack{}, U32.is_lt(uu, 32))
        == Pull.S{Pull.MCopy{Chr{uu} <> buf}, stack, Pull.GNext{}, done, False{}} : Pull.St}, nb92(uu, e92, ecls))

    case Lex.CPunct{tt}:
      ec = Equal.sym(Bool, U32.is_lt(uu, 32), False{}, ect)
      %ec : {Pull.copy.hit.go(Chr{uu}, tl, buf, stack, Pull.GNext{}, done, Lex.CPunct{tt}, _)
        == Pull.S{Pull.MCopy{Chr{uu} <> buf}, stack, Pull.GNext{}, done, False{}} : Pull.St}
      {==}
    case Lex.CSpace{}:
      ec = Equal.sym(Bool, U32.is_lt(uu, 32), False{}, ect)
      %ec : {Pull.copy.hit.go(Chr{uu}, tl, buf, stack, Pull.GNext{}, done, Lex.CSpace{}, _)
        == Pull.S{Pull.MCopy{Chr{uu} <> buf}, stack, Pull.GNext{}, done, False{}} : Pull.St}
      {==}
    case Lex.COther{}:
      ec = Equal.sym(Bool, U32.is_lt(uu, 32), False{}, ect)
      %ec : {Pull.copy.hit.go(Chr{uu}, tl, buf, stack, Pull.GNext{}, done, Lex.COther{}, _)
        == Pull.S{Pull.MCopy{Chr{uu} <> buf}, stack, Pull.GNext{}, done, False{}} : Pull.St}
      {==}

# a raw character, copied
law copy_raw:
  for +ch: Char
  for +h: {D1.raw_char(ch) == True{} : Bool}
  for +tl: String
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  {Pull.copy.hit.go(ch, tl, buf, stack, Pull.GNext{}, done, Lex.classify(ch), U32.is_lt(Char.to_u32(ch), 32))
    == Pull.S{Pull.MCopy{ch <> buf}, stack, Pull.GNext{}, done, False{}} : Pull.St}

def copy_raw(ch, h, tl, buf, stack, done):
  match ch:
    case Chr{+uu}:
      copy_go(Lex.classify(Chr{uu}), uu, {==}, raw34(uu, h), raw92(uu, h), rawlt(uu, h), tl, buf, stack, done)

# the escape copier's reversed prefix is the span scanner's
law crev0:
  for +src: String
  for nn: U32
  for acc: List<&2, Char>
  {Pull.copy.rev(src, nn, True{}, acc) == acc : List<&2, Char>}

def crev0(src, _nn, _acc):
  match src:
    case SNil{}:
      {==}
    case SCon{_, _}:
      {==}

law crev:
  for +src: String
  for +nn: U32
  for zz: Bool
  for +acc: List<&2, Char>
  {Pull.copy.rev(src, nn, zz, acc) == Lex.tokens.rev(src, nn, zz, acc) : List<&2, Char>}

def crev(src, nn, zz, acc):
  match src zz:
    case ss True{}:
      Equal.trans(List<&2, Char>, Pull.copy.rev(ss, nn, True{}, acc), acc, Lex.tokens.rev(ss, nn, True{}, acc),
        crev0(ss, nn, acc), Equal.sym(List<&2, Char>, Lex.tokens.rev(ss, nn, True{}, acc), acc, M2.rev_zero(ss, nn,
            acc)))
    case SNil{} False{}:
      {==}
    case SCon{+hd, +tl} False{}:
      crev(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), hd <> acc)

# the escape copier's reversed prefix of no characters
# a two-character escape, once the backslash is in: its character is copied
law et_esc.at:
  for isu: Bool
  for +uu: U32
  for eu: {U32.is_eq(uu, 117) == isu : Bool}
  for +h: {D2.has_char(D2.unesc(Chr{uu})) == True{} : Bool}
  for +rest: String
  for +bb: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for +ff: Nat
  {Pull.next.go(1n+ff, SCon{Chr{uu}, rest}, Pull.S{Pull.MEsc{bb}, stack, Pull.GNext{}, done, False{}})
    == Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(D2.PEsc{Chr{uu}}) <> bb}, stack, Pull.GNext{},
      done, False{}}) : Pull.Out}

def et_esc.at(isu, uu, eu, h, rest, bb, stack, done, ff):
  match isu:
    case True{}:
      ek = Equal.sym(U32, uu, 117, M15.ueq(uu, 117, eu))
      e2 = Equal.cong(U32, Bool, zz => D2.has_char(D2.unesc(Chr{zz})), 117, uu, ek)
      M6.no({Pull.next.go(1n+ff, SCon{Chr{uu}, rest}, Pull.S{Pull.MEsc{bb}, stack, Pull.GNext{}, done, False{}})
        == Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(D2.PEsc{Chr{uu}}) <> bb}, stack, Pull.GNext{},
          done, False{}}) : Pull.Out}, Equal.trans(Bool, False{}, D2.has_char(D2.unesc(Chr{uu})), True{}, e2, h))
    case False{}:
      es = Equal.sym(Bool, U32.is_eq(uu, 117), False{}, eu)
      %es : {Pull.next.go(1n+ff, rest, Pull.esc.hit.go(Chr{uu}, rest, bb, stack, Pull.GNext{}, done, _))
        == Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(D2.PEsc{Chr{uu}}) <> bb}, stack,
          Pull.GNext{}, done, False{}}) : Pull.Out}
      ms = Equal.sym(Maybe<&2, Char>, D2.unesc(Chr{uu}), Some{D2.some_or(D2.unesc(Chr{uu}), Chr{uu})},
        M13.some_is(D2.unesc(Chr{uu}), Chr{uu}, h))
      %ms : {Pull.next.go(1n+ff, rest, Pull.esc.put(rest, bb, stack, Pull.GNext{}, done, _))
        == Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(D2.PEsc{Chr{uu}}) <> bb}, stack,
          Pull.GNext{}, done, False{}}) : Pull.Out}
      {==}

law et_esc:
  for +ch: Char
  for h: {D2.has_char(D2.unesc(ch)) == True{} : Bool}
  for +rest: String
  for +bb: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for +ff: Nat
  {Pull.next.go(1n+ff, SCon{ch, rest}, Pull.S{Pull.MEsc{bb}, stack, Pull.GNext{}, done, False{}})
    == Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(D2.PEsc{ch}) <> bb}, stack, Pull.GNext{}, done,
      False{}}) : Pull.Out}

def et_esc(ch, h, rest, bb, stack, done, ff):
  match ch:
    case Chr{+uu}:
      et_esc.at(U32.is_eq(uu, 117), uu, {==}, h, rest, bb, stack, done, ff)

# et_esc, once whether the character is u is named
# one hex digit of a \u escape
law dig_u:
  for +ch: Char
  for h: {D2.hexd(ch) == True{} : Bool}
  for +tl: String
  for left: Nat
  for +acc: U32
  for +bb: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for +ff: Nat
  {Pull.next.go(1n+ff, SCon{ch, tl}, Pull.S{Pull.MUni{left, acc, bb}, stack, Pull.GNext{}, done, False{}})
    == Pull.next.go(1n+ff, tl, Pull.uni.put(tl, left, acc, Lex.hex(ch), bb, stack, Pull.GNext{}, done)) : Pull.Out}

def dig_u(ch, h, tl, left, acc, bb, stack, done, ff):
  hs = Equal.sym(Bool, D2.hexd(ch), True{}, h)
  %hs : {Pull.next.go(1n+ff, tl, Pull.uni.hit.go(ch, tl, left, acc, bb, stack, Pull.GNext{}, done, _))
    == Pull.next.go(1n+ff, tl, Pull.uni.put(tl, left, acc, Lex.hex(ch), bb, stack, Pull.GNext{}, done)) : Pull.Out}
  {==}

# one hex digit of a low surrogate's \u escape
law dig_l:
  for +ch: Char
  for h: {D2.hexd(ch) == True{} : Bool}
  for +tl: String
  for left: Nat
  for +acc: U32
  for +hi: U32
  for +bb: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for +ff: Nat
  {Pull.next.go(1n+ff, SCon{ch, tl}, Pull.S{Pull.MLo{left, acc, hi, bb}, stack, Pull.GNext{}, done, False{}})
    == Pull.next.go(1n+ff, tl, Pull.lo.put(tl, left, acc, hi, Lex.hex(ch), bb, stack, Pull.GNext{}, done)) : Pull.Out}

def dig_l(ch, h, tl, left, acc, hi, bb, stack, done, ff):
  hs = Equal.sym(Bool, D2.hexd(ch), True{}, h)
  %hs : {Pull.next.go(1n+ff, tl, Pull.lo.hit.go(ch, tl, left, acc, hi, bb, stack, Pull.GNext{}, done, _))
    == Pull.next.go(1n+ff, tl, Pull.lo.put(tl, left, acc, hi, Lex.hex(ch), bb, stack, Pull.GNext{}, done)) : Pull.Out}
  {==}

# a \u escape's four digits, once the backslash is in: its character is copied
law et_u:
  for +aa: Char
  for +bb: Char
  for +cc: Char
  for +dd: Char
  for +h: {D2.piece.ok(D2.PU{aa, bb, cc, dd}) == True{} : Bool}
  for +rest: String
  for +bf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for +ff: Nat
  {Pull.next.go(1n+ff, SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, rest}}}}}, Pull.S{Pull.MEsc{bf}, stack,
    Pull.GNext{}, done, False{}})
    == Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(D2.PU{aa, bb, cc, dd}) <> bf}, stack,
      Pull.GNext{}, done, False{}}) : Pull.Out}

def et_u(aa, bb, cc, dd, h, rest, bf, stack, done, ff):
  +hh = M6.and_left(Bool.and(D2.hexd(aa), Bool.and(D2.hexd(bb), Bool.and(D2.hexd(cc), D2.hexd(dd)))),
    D2.non_sur(D2.hex4(aa, bb, cc, dd)), h)
  hn = M6.and_right(Bool.and(D2.hexd(aa), Bool.and(D2.hexd(bb), Bool.and(D2.hexd(cc), D2.hexd(dd)))),
    D2.non_sur(D2.hex4(aa, bb, cc, dd)), h)
  +fin = Equal.cong(Lex.Sur, Pull.Out, zz => Pull.next.go(1n+ff, rest, Pull.uni.end.go(rest,
    D2.hex4(aa, bb, cc, dd), bf, stack, Pull.GNext{}, done, zz)), Lex.unicode.sur(D2.hex4(aa, bb, cc, dd)),
      Lex.SOk{},
    M3.sur_ok(D2.hex4(aa, bb, cc, dd), hn))
  Equal.trans(Pull.Out, Pull.next.go(1n+ff, SCon{aa, SCon{bb, SCon{cc, SCon{dd, rest}}}}, Pull.S{Pull.MUni{3n, 0, bf},
    stack, Pull.GNext{}, done, False{}}), Pull.next.go(1n+ff, SCon{bb, SCon{cc, SCon{dd, rest}}}, Pull.S{Pull.MUni{2n,
    D2.hex.acc(0, aa), bf}, stack, Pull.GNext{}, done, False{}}), Pull.next.go(1n+ff, rest,
    Pull.S{Pull.MCopy{D2.piece.char(D2.PU{aa, bb, cc, dd}) <> bf}, stack, Pull.GNext{}, done, False{}}), dig_u(aa,
    M3.and4_1(D2.hexd(aa), D2.hexd(bb), D2.hexd(cc), D2.hexd(dd), hh), SCon{bb, SCon{cc, SCon{dd, rest}}}, 3n, 0,
    bf, stack, done, ff),
    Equal.trans(Pull.Out, Pull.next.go(1n+ff, SCon{bb, SCon{cc, SCon{dd, rest}}}, Pull.S{Pull.MUni{2n, D2.hex.acc(0,
      aa), bf}, stack, Pull.GNext{}, done, False{}}), Pull.next.go(1n+ff, SCon{cc, SCon{dd, rest}},
      Pull.S{Pull.MUni{1n, D2.hex.acc(D2.hex.acc(0, aa), bb), bf}, stack, Pull.GNext{}, done, False{}}),
      Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(D2.PU{aa, bb, cc, dd}) <> bf}, stack, Pull.GNext{},
      done, False{}}), dig_u(bb, M3.and4_2(D2.hexd(aa), D2.hexd(bb), D2.hexd(cc), D2.hexd(dd), hh), SCon{cc,
      SCon{dd, rest}}, 2n, D2.hex.acc(0, aa), bf, stack, done, ff),
    Equal.trans(Pull.Out, Pull.next.go(1n+ff, SCon{cc, SCon{dd, rest}}, Pull.S{Pull.MUni{1n,
      D2.hex.acc(D2.hex.acc(0, aa), bb), bf}, stack, Pull.GNext{}, done, False{}}), Pull.next.go(1n+ff, SCon{dd,
      rest}, Pull.S{Pull.MUni{0n, D2.hex.acc(D2.hex.acc(D2.hex.acc(0, aa), bb), cc), bf}, stack, Pull.GNext{},
      done, False{}}), Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(D2.PU{aa, bb, cc, dd}) <> bf},
      stack, Pull.GNext{}, done, False{}}), dig_u(cc, M3.and4_3(D2.hexd(aa), D2.hexd(bb), D2.hexd(cc),
      D2.hexd(dd), hh), SCon{dd, rest}, 1n, D2.hex.acc(D2.hex.acc(0, aa), bb), bf, stack, done, ff),
    Equal.trans(Pull.Out, Pull.next.go(1n+ff, SCon{dd, rest}, Pull.S{Pull.MUni{0n,
      D2.hex.acc(D2.hex.acc(D2.hex.acc(0, aa), bb), cc), bf}, stack, Pull.GNext{}, done, False{}}),
      Pull.next.go(1n+ff, rest, Pull.uni.put(rest, 0n, D2.hex.acc(D2.hex.acc(D2.hex.acc(0, aa), bb), cc),
      Lex.hex(dd), bf, stack, Pull.GNext{}, done)), Pull.next.go(1n+ff, rest,
      Pull.S{Pull.MCopy{D2.piece.char(D2.PU{aa, bb, cc, dd}) <> bf}, stack, Pull.GNext{}, done, False{}}),
      dig_u(dd, M3.and4_4(D2.hexd(aa), D2.hexd(bb), D2.hexd(cc), D2.hexd(dd), hh), rest, 0n,
      D2.hex.acc(D2.hex.acc(D2.hex.acc(0, aa), bb), cc), bf, stack, done, ff), fin))))

# a surrogate pair's escapes, once the first backslash is in: its character is copied
law et_pair:
  for +h1: Char
  for +h2: Char
  for +h3: Char
  for +h4: Char
  for +l1: Char
  for +l2: Char
  for +l3: Char
  for +l4: Char
  for +h: {D2.piece.ok(D2.PPair{h1, h2, h3, h4, l1, l2, l3, l4}) == True{} : Bool}
  for +rest: String
  for +bf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for +ff: Nat
  {Pull.next.go(1n+ff, SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3,
    SCon{l4, rest}}}}}}}}}}}, Pull.S{Pull.MEsc{bf}, stack, Pull.GNext{},
    done, False{}})
    == Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(D2.PPair{h1, h2, h3, h4, l1, l2, l3, l4}) <> bf},
      stack, Pull.GNext{}, done, False{}}) : Pull.Out}

def et_pair(h1, h2, h3, h4, l1, l2, l3, l4, h, rest, bf, stack, done, ff):
  +hh = M6.and_left(Bool.and(D2.hexd(h1), Bool.and(D2.hexd(h2), Bool.and(D2.hexd(h3), D2.hexd(h4)))),
    Bool.and(Bool.and(D2.hexd(l1), Bool.and(D2.hexd(l2), Bool.and(D2.hexd(l3), D2.hexd(l4)))),
    Bool.and(D2.in_hi(D2.hex4(h1, h2, h3, h4)), D2.lo_sur(D2.hex4(l1, l2, l3, l4)))), h)
  +r1 = M6.and_right(Bool.and(D2.hexd(h1), Bool.and(D2.hexd(h2), Bool.and(D2.hexd(h3), D2.hexd(h4)))),
    Bool.and(Bool.and(D2.hexd(l1), Bool.and(D2.hexd(l2), Bool.and(D2.hexd(l3), D2.hexd(l4)))),
    Bool.and(D2.in_hi(D2.hex4(h1, h2, h3, h4)), D2.lo_sur(D2.hex4(l1, l2, l3, l4)))), h)
  +hl = M6.and_left(Bool.and(D2.hexd(l1), Bool.and(D2.hexd(l2), Bool.and(D2.hexd(l3), D2.hexd(l4)))),
    Bool.and(D2.in_hi(D2.hex4(h1, h2, h3, h4)), D2.lo_sur(D2.hex4(l1, l2, l3, l4))), r1)
  +r2 = M6.and_right(Bool.and(D2.hexd(l1), Bool.and(D2.hexd(l2), Bool.and(D2.hexd(l3), D2.hexd(l4)))),
    Bool.and(D2.in_hi(D2.hex4(h1, h2, h3, h4)), D2.lo_sur(D2.hex4(l1, l2, l3, l4))), r1)
  hhi = M6.and_left(D2.in_hi(D2.hex4(h1, h2, h3, h4)), D2.lo_sur(D2.hex4(l1, l2, l3, l4)), r2)
  hlo = M6.and_right(D2.in_hi(D2.hex4(h1, h2, h3, h4)), D2.lo_sur(D2.hex4(l1, l2, l3, l4)), r2)
  +fin = Equal.cong(Lex.Sur, Pull.Out, zz => Pull.next.go(1n+ff, rest, Pull.lo.end.go(rest, D2.hex4(l1, l2, l3, l4),
    D2.hex4(h1, h2, h3, h4), bf, stack,
    Pull.GNext{}, done, zz)), Lex.unicode.sur(D2.hex4(l1, l2, l3, l4)), Lex.SLo{}, M3.sur_lo(D2.hex4(l1, l2, l3, l4),
      hlo))
  +mid = Equal.cong(Lex.Sur, Pull.Out, zz => Pull.next.go(1n+ff, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3,
    SCon{l4, rest}}}}}}, Pull.uni.end.go(SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4, rest}}}}}},
    D2.hex4(h1, h2, h3, h4), bf, stack,
    Pull.GNext{}, done, zz)), Lex.unicode.sur(D2.hex4(h1, h2, h3, h4)), Lex.SHi{}, M3.sur_hi(D2.hex4(h1, h2, h3, h4),
      hhi))
  Equal.trans(Pull.Out, Pull.next.go(1n+ff, SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2,
    SCon{l3, SCon{l4, rest}}}}}}}}}}, Pull.S{Pull.MUni{3n, 0, bf}, stack, Pull.GNext{}, done, False{}}),
    Pull.next.go(1n+ff, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4,
    rest}}}}}}}}}, Pull.S{Pull.MUni{2n, D2.hex.acc(0, h1), bf}, stack, Pull.GNext{}, done, False{}}),
    Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(D2.PPair{h1, h2, h3, h4, l1, l2, l3, l4}) <> bf},
    stack, Pull.GNext{}, done, False{}}), dig_u(h1, M3.and4_1(D2.hexd(h1), D2.hexd(h2), D2.hexd(h3), D2.hexd(h4),
    hh), SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4, rest}}}}}}}}}, 3n, 0, bf,
    stack, done, ff),
    Equal.trans(Pull.Out, Pull.next.go(1n+ff, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2,
      SCon{l3, SCon{l4, rest}}}}}}}}}, Pull.S{Pull.MUni{2n, D2.hex.acc(0, h1), bf}, stack, Pull.GNext{}, done,
      False{}}), Pull.next.go(1n+ff, SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4,
      rest}}}}}}}}, Pull.S{Pull.MUni{1n, D2.hex.acc(D2.hex.acc(0, h1), h2), bf}, stack, Pull.GNext{}, done,
      False{}}), Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(D2.PPair{h1, h2, h3, h4, l1, l2, l3,
      l4}) <> bf}, stack, Pull.GNext{}, done, False{}}), dig_u(h2, M3.and4_2(D2.hexd(h1), D2.hexd(h2), D2.hexd(h3),
      D2.hexd(h4), hh), SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4, rest}}}}}}}}, 2n,
      D2.hex.acc(0, h1), bf, stack, done, ff),
    Equal.trans(Pull.Out, Pull.next.go(1n+ff, SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3,
      SCon{l4, rest}}}}}}}}, Pull.S{Pull.MUni{1n, D2.hex.acc(D2.hex.acc(0, h1), h2), bf}, stack, Pull.GNext{},
      done, False{}}), Pull.next.go(1n+ff, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4,
      rest}}}}}}}, Pull.S{Pull.MUni{0n, D2.hex.acc(D2.hex.acc(D2.hex.acc(0, h1), h2), h3), bf}, stack,
      Pull.GNext{}, done, False{}}), Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(D2.PPair{h1, h2, h3,
      h4, l1, l2, l3, l4}) <> bf}, stack, Pull.GNext{}, done, False{}}), dig_u(h3, M3.and4_3(D2.hexd(h1), D2.hexd(h2),
      D2.hexd(h3), D2.hexd(h4), hh), SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4, rest}}}}}}},
      1n, D2.hex.acc(D2.hex.acc(0, h1), h2), bf, stack, done, ff),
    Equal.trans(Pull.Out, Pull.next.go(1n+ff, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4,
      rest}}}}}}}, Pull.S{Pull.MUni{0n, D2.hex.acc(D2.hex.acc(D2.hex.acc(0, h1), h2), h3), bf}, stack,
      Pull.GNext{}, done, False{}}), Pull.next.go(1n+ff, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4,
      rest}}}}}}, Pull.uni.put(SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4, rest}}}}}}, 0n,
      D2.hex.acc(D2.hex.acc(D2.hex.acc(0, h1), h2), h3), Lex.hex(h4), bf, stack, Pull.GNext{}, done)),
      Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(D2.PPair{h1, h2, h3, h4, l1, l2, l3, l4}) <> bf},
      stack, Pull.GNext{}, done, False{}}), dig_u(h4, M3.and4_4(D2.hexd(h1), D2.hexd(h2), D2.hexd(h3),
      D2.hexd(h4), hh), SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4, rest}}}}}}, 0n,
      D2.hex.acc(D2.hex.acc(D2.hex.acc(0, h1), h2), h3), bf, stack, done, ff),
    Equal.trans(Pull.Out, Pull.next.go(1n+ff, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4, rest}}}}}},
      Pull.uni.put(SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4, rest}}}}}}, 0n,
      D2.hex.acc(D2.hex.acc(D2.hex.acc(0, h1), h2), h3), Lex.hex(h4), bf, stack, Pull.GNext{}, done)),
      Pull.next.go(1n+ff, SCon{l1, SCon{l2, SCon{l3, SCon{l4, rest}}}}, Pull.S{Pull.MLo{3n, 0, D2.hex4(h1, h2, h3,
      h4), bf}, stack, Pull.GNext{}, done, False{}}), Pull.next.go(1n+ff, rest,
      Pull.S{Pull.MCopy{D2.piece.char(D2.PPair{h1, h2, h3, h4, l1, l2, l3, l4}) <> bf}, stack, Pull.GNext{}, done,
      False{}}), mid,
    Equal.trans(Pull.Out, Pull.next.go(1n+ff, SCon{l1, SCon{l2, SCon{l3, SCon{l4, rest}}}}, Pull.S{Pull.MLo{3n, 0,
      D2.hex4(h1, h2, h3, h4), bf}, stack, Pull.GNext{}, done, False{}}), Pull.next.go(1n+ff, SCon{l2, SCon{l3,
      SCon{l4, rest}}}, Pull.S{Pull.MLo{2n, D2.hex.acc(0, l1), D2.hex4(h1, h2, h3, h4), bf}, stack, Pull.GNext{},
      done, False{}}), Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(D2.PPair{h1, h2, h3, h4, l1, l2,
      l3, l4}) <> bf}, stack, Pull.GNext{}, done, False{}}), dig_l(l1, M3.and4_1(D2.hexd(l1), D2.hexd(l2),
      D2.hexd(l3), D2.hexd(l4), hl), SCon{l2, SCon{l3, SCon{l4, rest}}}, 3n, 0, D2.hex4(h1, h2, h3, h4), bf,
      stack, done, ff),
    Equal.trans(Pull.Out, Pull.next.go(1n+ff, SCon{l2, SCon{l3, SCon{l4, rest}}}, Pull.S{Pull.MLo{2n, D2.hex.acc(0,
      l1), D2.hex4(h1, h2, h3, h4), bf}, stack, Pull.GNext{}, done, False{}}), Pull.next.go(1n+ff, SCon{l3, SCon{l4,
      rest}}, Pull.S{Pull.MLo{1n, D2.hex.acc(D2.hex.acc(0, l1), l2), D2.hex4(h1, h2, h3, h4), bf}, stack,
      Pull.GNext{}, done, False{}}), Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(D2.PPair{h1, h2, h3,
      h4, l1, l2, l3, l4}) <> bf}, stack, Pull.GNext{}, done, False{}}), dig_l(l2, M3.and4_2(D2.hexd(l1), D2.hexd(l2),
      D2.hexd(l3), D2.hexd(l4), hl), SCon{l3, SCon{l4, rest}}, 2n, D2.hex.acc(0, l1), D2.hex4(h1, h2, h3, h4),
      bf, stack, done, ff),
    Equal.trans(Pull.Out, Pull.next.go(1n+ff, SCon{l3, SCon{l4, rest}}, Pull.S{Pull.MLo{1n,
      D2.hex.acc(D2.hex.acc(0, l1), l2), D2.hex4(h1, h2, h3, h4), bf}, stack, Pull.GNext{}, done, False{}}),
      Pull.next.go(1n+ff, SCon{l4, rest}, Pull.S{Pull.MLo{0n, D2.hex.acc(D2.hex.acc(D2.hex.acc(0, l1), l2), l3),
      D2.hex4(h1, h2, h3, h4), bf}, stack, Pull.GNext{}, done, False{}}), Pull.next.go(1n+ff, rest,
      Pull.S{Pull.MCopy{D2.piece.char(D2.PPair{h1, h2, h3, h4, l1, l2, l3, l4}) <> bf}, stack, Pull.GNext{}, done,
      False{}}), dig_l(l3, M3.and4_3(D2.hexd(l1), D2.hexd(l2), D2.hexd(l3), D2.hexd(l4), hl), SCon{l4, rest}, 1n,
      D2.hex.acc(D2.hex.acc(0, l1), l2), D2.hex4(h1, h2, h3, h4), bf, stack, done, ff),
    Equal.trans(Pull.Out, Pull.next.go(1n+ff, SCon{l4, rest}, Pull.S{Pull.MLo{0n,
      D2.hex.acc(D2.hex.acc(D2.hex.acc(0, l1), l2), l3), D2.hex4(h1, h2, h3, h4), bf}, stack, Pull.GNext{},
      done, False{}}), Pull.next.go(1n+ff, rest, Pull.lo.put(rest, 0n, D2.hex.acc(D2.hex.acc(D2.hex.acc(0, l1),
      l2), l3), D2.hex4(h1, h2, h3, h4), Lex.hex(l4), bf, stack, Pull.GNext{}, done)), Pull.next.go(1n+ff, rest,
      Pull.S{Pull.MCopy{D2.piece.char(D2.PPair{h1, h2, h3, h4, l1, l2, l3, l4}) <> bf}, stack, Pull.GNext{}, done,
      False{}}), dig_l(l4, M3.and4_4(D2.hexd(l1), D2.hexd(l2), D2.hexd(l3), D2.hexd(l4), hl), rest, 0n,
      D2.hex.acc(D2.hex.acc(D2.hex.acc(0, l1), l2), l3), D2.hex4(h1, h2, h3, h4), bf, stack, done, ff),
      fin)))))))))

# the string mode after one piece, read from `x`
def pstep(m: Pull.Mode, pc: D2.Piece, bb: List<&2, Char>, x: String) -> Pull.Mode:
  match m pc:
    case Pull.MQuote{} D2.PRaw{_}:
      Pull.MSpan{x, 1}
    case Pull.MSpan{cut, nn} D2.PRaw{_}:
      Pull.MSpan{cut, U32.add(nn, 1)}
    case _ _:
      Pull.MCopy{D2.piece.char(pc) <> bb}

# what piece_go says: the walk over a piece, and what the next mode holds
def pg_ty(
  m: Pull.Mode,
  pc: D2.Piece,
  bb: List<&2, Char>,
  rest: String,
  stack: List<&2, Pull.Frame>,
  done: Bool,
  ff: Nat
) -> Type:
  ({Pull.next.go(1n+ff, D2.piece.text(pc) ++ rest, Pull.S{m, stack, Pull.GNext{}, done, False{}})
    == Pull.next.go(1n+ff, rest, Pull.S{pstep(m, pc, bb, D2.piece.text(pc) ++ rest), stack, Pull.GNext{}, done,
      False{}}) : Pull.Out}
    & M15.hold(pstep(m, pc, bb, D2.piece.text(pc) ++ rest), rest, D2.piece.char(pc) <> bb))

# a piece that is a raw character
def is_raw(pc: D2.Piece) -> Bool:
  match pc:
    case D2.PRaw{_}:
      True{}
    case _:
      False{}

# a piece's text after its backslash, then `rest`
def etail(pc: D2.Piece, rest: String) -> String:
  match pc:
    case D2.PRaw{ch}:
      SCon{ch, rest}
    case D2.PEsc{ch}:
      SCon{ch, rest}
    case D2.PU{aa, bb, cc, dd}:
      SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, rest}}}}}
    case D2.PPair{h1, h2, h3, h4, l1, l2, l3, l4}:
      SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4,
        rest}}}}}}}}}}}

# a piece other than a raw character, once its backslash has put the walk in
# the escape mode holding `bb`
law pg_esc:
  for +pc: D2.Piece
  for +h_ok: {D2.piece.ok(pc) == True{} : Bool}
  for +bb: List<&2, Char>
  for +rest: String
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for +ff: Nat
  for h_raw: {is_raw(pc) == False{} : Bool}
  {Pull.next.go(1n+ff, etail(pc, rest), Pull.S{Pull.MEsc{bb}, stack, Pull.GNext{}, done, False{}})
    == Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(pc) <> bb}, stack, Pull.GNext{}, done, False{}})
    : Pull.Out}

def pg_esc(pc, h_ok, bb, rest, stack, done, ff, h_raw):
  match pc:
    case D2.PRaw{+ch}:
      M6.no({Pull.next.go(1n+ff, etail(D2.PRaw{ch}, rest), Pull.S{Pull.MEsc{bb}, stack, Pull.GNext{}, done, False{}})
        == Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(D2.PRaw{ch}) <> bb}, stack, Pull.GNext{}, done,
          False{}}) : Pull.Out}, Equal.sym(Bool, True{}, False{}, h_raw))
    case D2.PEsc{+ch}:
      et_esc(ch, h_ok, rest, bb, stack, done, ff)
    case D2.PU{+aa, +b2, +cc, +dd}:
      et_u(aa, b2, cc, dd, h_ok, rest, bb, stack, done, ff)
    case D2.PPair{+h1, +h2, +h3, +h4, +l1, +l2, +l3, +l4}:
      et_pair(h1, h2, h3, h4, l1, l2, l3, l4, h_ok, rest, bb, stack, done, ff)

# a piece read in a copy
law pg_copy:
  for +buf: List<&2, Char>
  for +pc: D2.Piece
  for +bb: List<&2, Char>
  for +rest: String
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for +ff: Nat
  for +h_ok: {D2.piece.ok(pc) == True{} : Bool}
  for e: {buf == bb : List<&2, Char>}
  pg_ty(Pull.MCopy{buf}, pc, bb, rest, stack, done, ff)

def pg_copy(buf, pc, bb, rest, stack, done, ff, h_ok, e):
  match pc:
    case D2.PRaw{+ch}:
      es = Equal.sym(List<&2, Char>, buf, bb, e)
      %es : pg_ty(Pull.MCopy{_}, D2.PRaw{ch}, bb, rest, stack, done, ff)
      (Equal.cong(Pull.St, Pull.Out, zz => Pull.next.go(1n+ff, rest, zz), Pull.copy.hit.go(ch, rest, bb, stack,
        Pull.GNext{}, done, Lex.classify(ch), U32.is_lt(Char.to_u32(ch), 32)), Pull.S{Pull.MCopy{ch <> bb}, stack,
        Pull.GNext{}, done, False{}}, copy_raw(ch, h_ok, rest, bb, stack, done)), {==})
    case D2.PEsc{+ch}:
      es = Equal.sym(List<&2, Char>, buf, bb, e)
      %es : pg_ty(Pull.MCopy{_}, D2.PEsc{ch}, bb, rest, stack, done, ff)
      (pg_esc(D2.PEsc{ch}, h_ok, bb, rest, stack, done, ff, {==}), {==})
    case D2.PU{+aa, +b2, +cc, +dd}:
      es = Equal.sym(List<&2, Char>, buf, bb, e)
      %es : pg_ty(Pull.MCopy{_}, D2.PU{aa, b2, cc, dd}, bb, rest, stack, done, ff)
      (pg_esc(D2.PU{aa, b2, cc, dd}, h_ok, bb, rest, stack, done, ff, {==}), {==})
    case D2.PPair{+h1, +h2, +h3, +h4, +l1, +l2, +l3, +l4}:
      es = Equal.sym(List<&2, Char>, buf, bb, e)
      %es : pg_ty(Pull.MCopy{_}, D2.PPair{h1, h2, h3, h4, l1, l2, l3, l4}, bb, rest, stack, done, ff)
      (pg_esc(D2.PPair{h1, h2, h3, h4, l1, l2, l3, l4}, h_ok, bb, rest, stack, done, ff, {==}), {==})

# a piece other than a raw character, read in a span: the span is copied
law pg_span.esc:
  for +cut: String
  for +nn: U32
  for +pc: D2.Piece
  for +bb: List<&2, Char>
  for +rest: String
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for +ff: Nat
  for +h_ok: {D2.piece.ok(pc) == True{} : Bool}
  for e_r: {Lex.tokens.rev(cut, nn, U32.is_zero(nn), []) == bb : List<&2, Char>}
  for h_raw: {is_raw(pc) == False{} : Bool}
  {Pull.next.go(1n+ff, etail(pc, rest), Pull.S{Pull.MEsc{Pull.copy.rev(cut, nn, U32.is_zero(nn), [])}, stack,
    Pull.GNext{}, done, False{}})
    == Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(pc) <> bb}, stack, Pull.GNext{}, done, False{}})
    : Pull.Out}

def pg_span.esc(cut, nn, pc, bb, rest, stack, done, ff, h_ok, e_r, h_raw):
  eb = Equal.sym(List<&2, Char>, Pull.copy.rev(cut, nn, U32.is_zero(nn), []), bb, Equal.trans(List<&2, Char>,
    Pull.copy.rev(cut, nn, U32.is_zero(nn), []), Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), bb,
    crev(cut, nn, U32.is_zero(nn), []), e_r))
  %eb : {Pull.next.go(1n+ff, etail(pc, rest), Pull.S{Pull.MEsc{_}, stack, Pull.GNext{}, done, False{}})
    == Pull.next.go(1n+ff, rest, Pull.S{Pull.MCopy{D2.piece.char(pc) <> bb}, stack, Pull.GNext{}, done, False{}})
    : Pull.Out}
  pg_esc(pc, h_ok, bb, rest, stack, done, ff, h_raw)

law pg_span:
  for +cut: String
  for +nn: U32
  for +pc: D2.Piece
  for +bb: List<&2, Char>
  for +rest: String
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for +ff: Nat
  for +h_ok: {D2.piece.ok(pc) == True{} : Bool}
  for +e_d: {M15.sdrop(cut, nn, U32.is_zero(nn)) == D2.piece.text(pc) ++ rest : String}
  for +e_r: {Lex.tokens.rev(cut, nn, U32.is_zero(nn), []) == bb : List<&2, Char>}
  for +e_s: {D1.short(cut) == True{} : Bool}
  pg_ty(Pull.MSpan{cut, nn}, pc, bb, rest, stack, done, ff)

def pg_span(cut, nn, pc, bb, rest, stack, done, ff, h_ok, e_d, e_r, e_s):
  match pc:
    case D2.PRaw{+ch}:
      +top = M2.pos_ne(cut, nn, 4294967295, U32.is_zero(nn), {==}, e_s, ch, rest, e_d)
      (Equal.cong(Pull.Skind, Pull.Out, zz => Pull.next.go(1n+ff, rest, Pull.span.advance(zz, cut, nn, stack,
        Pull.GNext{}, done)), Pull.span.kind.of(ch), Pull.KGo{}, kind_raw(ch, h_ok)),
        (M2.sdrop_grow(cut, nn, U32.is_zero(nn), {==}, top, ch, rest, e_d),
          (Equal.trans(List<&2, Char>, Lex.tokens.rev(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), []),
            ch <> Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), ch <> bb,
            M2.rev_grow(cut, nn, U32.is_zero(nn), {==}, top, ch, rest, e_d, []),
            Equal.cong(List<&2, Char>, List<&2, Char>, xx => ch <> xx, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), bb,
              e_r)), e_s)))
    case D2.PEsc{+ch}:
      (pg_span.esc(cut, nn, D2.PEsc{ch}, bb, rest, stack, done, ff, h_ok, e_r, {==}), {==})
    case D2.PU{+aa, +b2, +cc, +dd}:
      (pg_span.esc(cut, nn, D2.PU{aa, b2, cc, dd}, bb, rest, stack, done, ff, h_ok, e_r, {==}), {==})
    case D2.PPair{+h1, +h2, +h3, +h4, +l1, +l2, +l3, +l4}:
      (pg_span.esc(cut, nn, D2.PPair{h1, h2, h3, h4, l1, l2, l3, l4}, bb, rest, stack, done, ff, h_ok, e_r, {==}),
        {==})

# a piece read just after the opening quote
law pg_quote:
  for +pc: D2.Piece
  for +bb: List<&2, Char>
  for +rest: String
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for +ff: Nat
  for +h_ok: {D2.piece.ok(pc) == True{} : Bool}
  for e_b: {bb == [] : List<&2, Char>}
  for +e_s: {D1.short(D2.piece.text(pc) ++ rest) == True{} : Bool}
  pg_ty(Pull.MQuote{}, pc, bb, rest, stack, done, ff)

def pg_quote(pc, bb, rest, stack, done, ff, h_ok, e_b, e_s):
  match pc:
    case D2.PRaw{+ch}:
      es = Equal.sym(List<&2, Char>, bb, [], e_b)
      %es : pg_ty(Pull.MQuote{}, D2.PRaw{ch}, _, rest, stack, done, ff)
      (Equal.cong(Pull.Skind, Pull.Out, zz => Pull.next.go(1n+ff, rest, Pull.quote.go(zz, ch, rest, stack,
        Pull.GNext{}, done)), Pull.span.kind.of(ch), Pull.KGo{}, kind_raw(ch, h_ok)),
        (M2.sdrop_zero(rest, rest, {==}), (M2.rev_zero(rest, 0, [ch]), e_s)))
    case D2.PEsc{+ch}:
      es = Equal.sym(List<&2, Char>, bb, [], e_b)
      %es : pg_ty(Pull.MQuote{}, D2.PEsc{ch}, _, rest, stack, done, ff)
      (pg_esc(D2.PEsc{ch}, h_ok, [], rest, stack, done, ff, {==}), {==})
    case D2.PU{+aa, +b2, +cc, +dd}:
      es = Equal.sym(List<&2, Char>, bb, [], e_b)
      %es : pg_ty(Pull.MQuote{}, D2.PU{aa, b2, cc, dd}, _, rest, stack, done, ff)
      (pg_esc(D2.PU{aa, b2, cc, dd}, h_ok, [], rest, stack, done, ff, {==}), {==})
    case D2.PPair{+h1, +h2, +h3, +h4, +l1, +l2, +l3, +l4}:
      es = Equal.sym(List<&2, Char>, bb, [], e_b)
      %es : pg_ty(Pull.MQuote{}, D2.PPair{h1, h2, h3, h4, l1, l2, l3, l4}, _, rest, stack, done, ff)
      (pg_esc(D2.PPair{h1, h2, h3, h4, l1, l2, l3, l4}, h_ok, [], rest, stack, done, ff, {==}), {==})

# a piece, read in whatever string mode holds the characters so far
law piece_go:
  for +m: Pull.Mode
  for +pc: D2.Piece
  for +bb: List<&2, Char>
  for +rest: String
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for +ff: Nat
  for +h_ok: {D2.piece.ok(pc) == True{} : Bool}
  for h_h: M15.hold(m, D2.piece.text(pc) ++ rest, bb)
  pg_ty(m, pc, bb, rest, stack, done, ff)

def piece_go(m, pc, bb, rest, stack, done, ff, h_ok, h_h):
  match m:
    case Pull.MQuote{}:
      (e_b, e_s) = h_h
      pg_quote(pc, bb, rest, stack, done, ff, h_ok, e_b, e_s)
    case Pull.MSpan{+cut, +nn}:
      (e_d, (e_r, e_s)) = h_h
      pg_span(cut, nn, pc, bb, rest, stack, done, ff, h_ok, e_d, e_r, e_s)
    case Pull.MCopy{+buf}:
      pg_copy(buf, pc, bb, rest, stack, done, ff, h_ok, h_h)
    case Pull.MIdle{}:
      Empty.absurd(pg_ty(Pull.MIdle{}, pc, bb, rest, stack, done, ff), h_h)
    case Pull.MWord{a1, a2, a3}:
      Empty.absurd(pg_ty(Pull.MWord{a1, a2, a3}, pc, bb, rest, stack, done, ff), h_h)
    case Pull.MEsc{a1}:
      Empty.absurd(pg_ty(Pull.MEsc{a1}, pc, bb, rest, stack, done, ff), h_h)
    case Pull.MUni{a1, a2, a3}:
      Empty.absurd(pg_ty(Pull.MUni{a1, a2, a3}, pc, bb, rest, stack, done, ff), h_h)
    case Pull.MHi{a1, a2}:
      Empty.absurd(pg_ty(Pull.MHi{a1, a2}, pc, bb, rest, stack, done, ff), h_h)
    case Pull.MHiEsc{a1, a2}:
      Empty.absurd(pg_ty(Pull.MHiEsc{a1, a2}, pc, bb, rest, stack, done, ff), h_h)
    case Pull.MLo{a1, a2, a3, a4}:
      Empty.absurd(pg_ty(Pull.MLo{a1, a2, a3, a4}, pc, bb, rest, stack, done, ff), h_h)
    case Pull.MSkStr{}:
      Empty.absurd(pg_ty(Pull.MSkStr{}, pc, bb, rest, stack, done, ff), h_h)
    case Pull.MSkEsc{}:
      Empty.absurd(pg_ty(Pull.MSkEsc{}, pc, bb, rest, stack, done, ff), h_h)
    case Pull.MSkUni{a1, a2}:
      Empty.absurd(pg_ty(Pull.MSkUni{a1, a2}, pc, bb, rest, stack, done, ff), h_h)
    case Pull.MSkHi{a1}:
      Empty.absurd(pg_ty(Pull.MSkHi{a1}, pc, bb, rest, stack, done, ff), h_h)
    case Pull.MSkHiEsc{a1}:
      Empty.absurd(pg_ty(Pull.MSkHiEsc{a1}, pc, bb, rest, stack, done, ff), h_h)
    case Pull.MSkLo{a1, a2, a3}:
      Empty.absurd(pg_ty(Pull.MSkLo{a1, a2, a3}, pc, bb, rest, stack, done, ff), h_h)
    case Pull.MDone{a1, a2}:
      Empty.absurd(pg_ty(Pull.MDone{a1, a2}, pc, bb, rest, stack, done, ff), h_h)
    case Pull.MRest{a1}:
      Empty.absurd(pg_ty(Pull.MRest{a1}, pc, bb, rest, stack, done, ff), h_h)
    case Pull.MJump{a1, a2}:
      Empty.absurd(pg_ty(Pull.MJump{a1, a2}, pc, bb, rest, stack, done, ff), h_h)

# a character in front of a buffer
def ccons(ch: Char, bb: List<&2, Char>) -> List<&2, Char>:
  ch <> bb

# the string mode after pieces, read in front of `tail`
def psteps(ps: List<&2, D2.Piece>, m: Pull.Mode, +bb: List<&2, Char>, +tail: String) -> Pull.Mode:
  match ps:
    case Nil{}:
      m
    case +pc <> +tl:
      psteps(tl, pstep(m, pc, bb, M1.sp(pc <> tl, tail)), D2.piece.char(pc) <> bb, tail)

# the characters pieces stand for, reversed onto bb
def pcs(ps: List<&2, D2.Piece>, bb: List<&2, Char>) -> List<&2, Char>:
  match ps:
    case Nil{}:
      bb
    case +pc <> tl:
      pcs(tl, D2.piece.char(pc) <> bb)

# what pieces_go says: the walk over pieces, and what the mode after them holds
def pcs_ty(
  ps: List<&2, D2.Piece>,
  m: Pull.Mode,
  bb: List<&2, Char>,
  tail: String,
  stack: List<&2, Pull.Frame>,
  done: Bool,
  ff: Nat
) -> Type:
  ({Pull.next.go(1n+ff, M1.sp(ps, tail), Pull.S{m, stack, Pull.GNext{}, done, False{}})
    == Pull.next.go(1n+ff, tail, Pull.S{psteps(ps, m, bb, tail), stack, Pull.GNext{}, done, False{}}) : Pull.Out}
    & M15.hold(psteps(ps, m, bb, tail), tail, pcs(ps, bb)))

# pieces_go, once the first piece's walk and the rest's are in hand
law pieces_go.fin:
  for +pc: D2.Piece
  for +tl: List<&2, D2.Piece>
  for +m: Pull.Mode
  for +bb: List<&2, Char>
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for +ff: Nat
  for e1: {Pull.next.go(1n+ff, D2.piece.text(pc) ++ M1.sp(tl, tail), Pull.S{m, stack, Pull.GNext{}, done, False{}})
    == Pull.next.go(1n+ff, M1.sp(tl, tail), Pull.S{pstep(m, pc, bb, M1.sp(pc <> tl, tail)), stack, Pull.GNext{}, done,
      False{}}) : Pull.Out}
  for rr: pcs_ty(tl, pstep(m, pc, bb, M1.sp(pc <> tl, tail)), D2.piece.char(pc) <> bb, tail, stack, done, ff)
  pcs_ty(pc <> tl, m, bb, tail, stack, done, ff)

def pieces_go.fin(pc, tl, m, bb, tail, stack, done, ff, e1, rr):
  (e2, hh) = rr
  +m2 = pstep(m, pc, bb, M1.sp(pc <> tl, tail))
  +b2 = ccons(D2.piece.char(pc), bb)
  (Equal.trans(Pull.Out, Pull.next.go(1n+ff, M1.sp(pc <> tl, tail), Pull.S{m, stack, Pull.GNext{}, done, False{}}),
    Pull.next.go(1n+ff, M1.sp(tl, tail), Pull.S{m2, stack, Pull.GNext{}, done, False{}}),
    Pull.next.go(1n+ff, tail, Pull.S{psteps(tl, m2, b2, tail), stack, Pull.GNext{}, done, False{}}), e1, e2), hh)

# pieces_go, one piece on, the rest given
law pieces_go.cons:
  for +pc: D2.Piece
  for +tl: List<&2, D2.Piece>
  for +m: Pull.Mode
  for +bb: List<&2, Char>
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for +ff: Nat
  for gg: pg_ty(m, pc, bb, M1.sp(tl, tail), stack, done, ff)
  for ih: M15.hold(pstep(m, pc, bb, M1.sp(pc <> tl, tail)), M1.sp(tl, tail), D2.piece.char(pc) <> bb)
    -> pcs_ty(tl, pstep(m, pc, bb, M1.sp(pc <> tl, tail)), D2.piece.char(pc) <> bb, tail, stack, done, ff)
  pcs_ty(pc <> tl, m, bb, tail, stack, done, ff)

def pieces_go.cons(pc, tl, m, bb, tail, stack, done, ff, gg, ih):
  (e1, hh) = gg
  pieces_go.fin(pc, tl, m, bb, tail, stack, done, ff, e1, ih(hh))

# pieces, read in whatever string mode holds the characters so far
law pieces_go:
  for +ps: List<&2, D2.Piece>
  for +m: Pull.Mode
  for +bb: List<&2, Char>
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for +ff: Nat
  for +h_ok: {D2.spell_ok(ps) == True{} : Bool}
  for h_h: M15.hold(m, M1.sp(ps, tail), bb)
  pcs_ty(ps, m, bb, tail, stack, done, ff)

def pieces_go(ps, m, bb, tail, stack, done, ff, h_ok, h_h):
  match ps:
    case Nil{}:
      ({==}, h_h)
    case +pc <> +tl:
      +hp = M6.and_left(D2.piece.ok(pc), D2.spell_ok(tl), h_ok)
      +ht = M6.and_right(D2.piece.ok(pc), D2.spell_ok(tl), h_ok)
      pieces_go.cons(pc, tl, m, bb, tail, stack, done, ff, piece_go(m, pc, bb, M1.sp(tl, tail), stack, done, ff, hp,
          h_h),
        hh => pieces_go(tl, pstep(m, pc, bb, M1.sp(pc <> tl, tail)), D2.piece.char(pc) <> bb, tail, stack, done, ff, ht,
          hh))

# pieces' characters reversed onto a buffer, read back
law text_pcs.go:
  for +ps: List<&2, D2.Piece>
  for +acc: List<&2, Char>
  for +ss: String
  {Lex.text.go(pcs(ps, acc), ss) == Lex.text.go(acc, D2.spelled(ps) ++ ss) : String}

def text_pcs.go(ps, acc, ss):
  match ps:
    case Nil{}:
      {==}
    case +pc <> +tl:
      text_pcs.go(tl, D2.piece.char(pc) <> acc, ss)

# pieces' characters, reversed, read back, are the characters they stand for
law text_pcs:
  for +ps: List<&2, D2.Piece>
  {Lex.text(pcs(ps, [])) == D2.spelled(ps) : String}

def text_pcs(ps):
  Equal.trans(String, Lex.text(pcs(ps, [])), D2.spelled(ps) ++ "", D2.spelled(ps), text_pcs.go(ps, [], ""),
    M6.append_nil(D2.spelled(ps)))

# a value slot is a slot a string may go
law val_str:
  for +stack: List<&2, Pull.Frame>
  for h_v: {Pull.expect.val.go(stack) == True{} : Bool}
  {Pull.expect.str.go(stack) == True{} : Bool}

def val_str(stack, h_v):
  match stack:
    case Nil{}:
      {==}
    case Pull.FArr{Pull.SVal{}, _} <> _:
      {==}
    case Pull.FObj{Pull.SVal{}, _} <> _:
      {==}
    case Pull.FArr{Pull.SCom{}, _} <> _:
      h_v
    case Pull.FArr{Pull.SKey{}, _} <> _:
      h_v
    case Pull.FArr{Pull.SCol{}, _} <> _:
      h_v
    case Pull.FObj{Pull.SCom{}, _} <> _:
      h_v
    case Pull.FObj{Pull.SKey{}, _} <> _:
      M6.no({True{} == True{} : Bool}, h_v)
    case Pull.FObj{Pull.SCol{}, _} <> _:
      h_v

# laws/CursorEventsMatchParse.bend, a string's closing quote

# a string closed on the suffix in hand lands where a value may go
law sph_v:
  for +pc: Pull.Piece
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for h_v: {Pull.expect.val.go(stack) == True{} : Bool}
  for +ff: Nat
  {Pull.next.go(1n+ff, tail, Pull.str.place.here(pc, stack, Pull.GNext{})) == Pull.Fin{(Pull.SEv{Pull.str.ev(pc,
    False{})}, M4.aft(tail, stack))} : Pull.Out}

def sph_v(pc, tail, stack, h_v, ff):
  match stack:
    case Nil{}:
      go_rest(ff, tail, Pull.SEv{Pull.str.ev(pc, False{})}, [], Pull.GNext{}, True{}, False{})
    case Pull.FArr{Pull.SVal{}, fr} <> +oo:
      go_rest(ff, tail, Pull.SEv{Pull.str.ev(pc, False{})}, Pull.FArr{Pull.SCom{}, False{}} <> oo, Pull.GNext{},
        False{}, False{})
    case Pull.FObj{Pull.SVal{}, fr} <> +oo:
      go_rest(ff, tail, Pull.SEv{Pull.str.ev(pc, False{})}, Pull.FObj{Pull.SCom{}, False{}} <> oo, Pull.GNext{},
        False{}, False{})
    case Pull.FArr{Pull.SCom{}, fr} <> oo:
      M6.no({Pull.next.go(1n+ff, tail, Pull.str.place.here(pc, Pull.FArr{Pull.SCom{}, fr} <> oo,
        Pull.GNext{})) == Pull.Fin{(Pull.SEv{Pull.str.ev(pc, False{})}, M4.aft(tail, Pull.FArr{Pull.SCom{},
        fr} <> oo))} : Pull.Out}, h_v)
    case Pull.FArr{Pull.SKey{}, fr} <> oo:
      M6.no({Pull.next.go(1n+ff, tail, Pull.str.place.here(pc, Pull.FArr{Pull.SKey{}, fr} <> oo,
        Pull.GNext{})) == Pull.Fin{(Pull.SEv{Pull.str.ev(pc, False{})}, M4.aft(tail, Pull.FArr{Pull.SKey{},
        fr} <> oo))} : Pull.Out}, h_v)
    case Pull.FArr{Pull.SCol{}, fr} <> oo:
      M6.no({Pull.next.go(1n+ff, tail, Pull.str.place.here(pc, Pull.FArr{Pull.SCol{}, fr} <> oo,
        Pull.GNext{})) == Pull.Fin{(Pull.SEv{Pull.str.ev(pc, False{})}, M4.aft(tail, Pull.FArr{Pull.SCol{},
        fr} <> oo))} : Pull.Out}, h_v)
    case Pull.FObj{Pull.SCom{}, fr} <> oo:
      M6.no({Pull.next.go(1n+ff, tail, Pull.str.place.here(pc, Pull.FObj{Pull.SCom{}, fr} <> oo,
        Pull.GNext{})) == Pull.Fin{(Pull.SEv{Pull.str.ev(pc, False{})}, M4.aft(tail, Pull.FObj{Pull.SCom{},
        fr} <> oo))} : Pull.Out}, h_v)
    case Pull.FObj{Pull.SKey{}, fr} <> oo:
      M6.no({Pull.next.go(1n+ff, tail, Pull.str.place.here(pc, Pull.FObj{Pull.SKey{}, fr} <> oo,
        Pull.GNext{})) == Pull.Fin{(Pull.SEv{Pull.str.ev(pc, False{})}, M4.aft(tail, Pull.FObj{Pull.SKey{},
        fr} <> oo))} : Pull.Out}, h_v)
    case Pull.FObj{Pull.SCol{}, fr} <> oo:
      M6.no({Pull.next.go(1n+ff, tail, Pull.str.place.here(pc, Pull.FObj{Pull.SCol{}, fr} <> oo,
        Pull.GNext{})) == Pull.Fin{(Pull.SEv{Pull.str.ev(pc, False{})}, M4.aft(tail, Pull.FObj{Pull.SCol{},
        fr} <> oo))} : Pull.Out}, h_v)

# a decoded string closed lands where a value may go
law sp_v:
  for +pc: Pull.Piece
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for h_v: {Pull.expect.val.go(stack) == True{} : Bool}
  for +ff: Nat
  {Pull.next.go(1n+ff, tail, Pull.str.place(pc, tail, stack, Pull.GNext{})) == Pull.Fin{(Pull.SEv{Pull.str.ev(pc,
    False{})}, M4.aft(tail, stack))} : Pull.Out}

def sp_v(pc, tail, stack, h_v, ff):
  match stack:
    case Nil{}:
      M8.go_done(ff, tail, Pull.SEv{Pull.str.ev(pc, False{})}, tail, [], Pull.GNext{}, True{}, False{})
    case Pull.FArr{Pull.SVal{}, fr} <> +oo:
      M8.go_done(ff, tail, Pull.SEv{Pull.str.ev(pc, False{})}, tail, Pull.FArr{Pull.SCom{}, False{}} <> oo,
          Pull.GNext{},
        False{}, False{})
    case Pull.FObj{Pull.SVal{}, fr} <> +oo:
      M8.go_done(ff, tail, Pull.SEv{Pull.str.ev(pc, False{})}, tail, Pull.FObj{Pull.SCom{}, False{}} <> oo,
          Pull.GNext{},
        False{}, False{})
    case Pull.FArr{Pull.SCom{}, fr} <> oo:
      M6.no({Pull.next.go(1n+ff, tail, Pull.str.place(pc, tail, Pull.FArr{Pull.SCom{}, fr} <> oo,
        Pull.GNext{})) == Pull.Fin{(Pull.SEv{Pull.str.ev(pc, False{})}, M4.aft(tail, Pull.FArr{Pull.SCom{},
        fr} <> oo))} : Pull.Out}, h_v)
    case Pull.FArr{Pull.SKey{}, fr} <> oo:
      M6.no({Pull.next.go(1n+ff, tail, Pull.str.place(pc, tail, Pull.FArr{Pull.SKey{}, fr} <> oo,
        Pull.GNext{})) == Pull.Fin{(Pull.SEv{Pull.str.ev(pc, False{})}, M4.aft(tail, Pull.FArr{Pull.SKey{},
        fr} <> oo))} : Pull.Out}, h_v)
    case Pull.FArr{Pull.SCol{}, fr} <> oo:
      M6.no({Pull.next.go(1n+ff, tail, Pull.str.place(pc, tail, Pull.FArr{Pull.SCol{}, fr} <> oo,
        Pull.GNext{})) == Pull.Fin{(Pull.SEv{Pull.str.ev(pc, False{})}, M4.aft(tail, Pull.FArr{Pull.SCol{},
        fr} <> oo))} : Pull.Out}, h_v)
    case Pull.FObj{Pull.SCom{}, fr} <> oo:
      M6.no({Pull.next.go(1n+ff, tail, Pull.str.place(pc, tail, Pull.FObj{Pull.SCom{}, fr} <> oo,
        Pull.GNext{})) == Pull.Fin{(Pull.SEv{Pull.str.ev(pc, False{})}, M4.aft(tail, Pull.FObj{Pull.SCom{},
        fr} <> oo))} : Pull.Out}, h_v)
    case Pull.FObj{Pull.SKey{}, fr} <> oo:
      M6.no({Pull.next.go(1n+ff, tail, Pull.str.place(pc, tail, Pull.FObj{Pull.SKey{}, fr} <> oo,
        Pull.GNext{})) == Pull.Fin{(Pull.SEv{Pull.str.ev(pc, False{})}, M4.aft(tail, Pull.FObj{Pull.SKey{},
        fr} <> oo))} : Pull.Out}, h_v)
    case Pull.FObj{Pull.SCol{}, fr} <> oo:
      M6.no({Pull.next.go(1n+ff, tail, Pull.str.place(pc, tail, Pull.FObj{Pull.SCol{}, fr} <> oo,
        Pull.GNext{})) == Pull.Fin{(Pull.SEv{Pull.str.ev(pc, False{})}, M4.aft(tail, Pull.FObj{Pull.SCol{},
        fr} <> oo))} : Pull.Out}, h_v)

# a string's closing quote, from whatever string mode holds its characters
law str_fin_v:
  for +mm: Pull.Mode
  for +bb: List<&2, Char>
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +h_v: {Pull.expect.val.go(stack) == True{} : Bool}
  for +xx: String
  for e0: {Pull.next.go(4n, SCon{'"', xx}, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, False{}, False{}})
    == Pull.next.go(4n, SCon{'"', tail}, Pull.S{mm, stack, Pull.GNext{}, False{}, False{}}) : Pull.Out}
  for hh: M15.hold(mm, SCon{'"', tail}, bb)
  strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{Lex.text(bb)}], M4.aft(tail, stack))

def str_fin_v(mm, bb, tail, stack, h_v, xx, e0, hh):
  match mm:
    case Pull.MQuote{}:
      (e_b, _e_s) = hh
      es = Equal.sym(List<&2, Char>, bb, [], e_b)
      %es : strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{Lex.text(_)}], M4.aft(tail, stack))
      strm_one(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, Pull.EStrS{"", 0}, M4.aft(tail, stack),
        next_fin(SCon{'"', xx}, stack, False{}, (Pull.SEv{Pull.EStrS{"", 0}}, M4.aft(tail, stack)),
        Equal.trans(Pull.Out, Pull.next.go(4n, SCon{'"', xx}, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, False{},
          False{}}),
          Pull.next.go(4n, SCon{'"', tail}, Pull.S{Pull.MQuote{}, stack, Pull.GNext{}, False{}, False{}}),
            Pull.Fin{(Pull.SEv{Pull.EStrS{"", 0}}, M4.aft(tail, stack))}, e0, sph_v(Pull.PSpan{"", 0}, tail, stack, h_v,
            3n))))
    case Pull.MSpan{+cut, +nn}:
      (_e_d, (e_r, _e_s)) = hh
      et = Equal.trans(String, D1.take(cut, U32.to_nat(nn)), V.span.str(cut, nn, U32.is_zero(nn)), Lex.text(bb),
        Equal.sym(String, V.span.str(cut, nn, U32.is_zero(nn)), D1.take(cut, U32.to_nat(nn)), M16.span_take(cut, nn)),
        Equal.trans(String, V.span.str(cut, nn, U32.is_zero(nn)), Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn),
          [])),
          Lex.text(bb), Equal.sym(String, Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])),
          V.span.str(cut, nn, U32.is_zero(nn)), M2.text_span(cut, nn, U32.is_zero(nn))),
          Equal.cong(List<&2, Char>, String, zz => Lex.text(zz), Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), bb,
            e_r)))
      %et : strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{_}], M4.aft(tail, stack))
      strm_one(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, Pull.EStrS{cut, nn}, M4.aft(tail, stack),
        next_fin(SCon{'"', xx}, stack, False{}, (Pull.SEv{Pull.EStrS{cut, nn}}, M4.aft(tail, stack)),
        Equal.trans(Pull.Out, Pull.next.go(4n, SCon{'"', xx}, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, False{},
          False{}}),
          Pull.next.go(4n, SCon{'"', tail}, Pull.S{Pull.MSpan{cut, nn}, stack, Pull.GNext{}, False{}, False{}}),
            Pull.Fin{(Pull.SEv{Pull.EStrS{cut, nn}}, M4.aft(tail, stack))}, e0, sph_v(Pull.PSpan{cut, nn}, tail, stack,
            h_v, 3n))))
    case Pull.MCopy{+buf}:
      et = Equal.cong(List<&2, Char>, String, zz => Lex.text(zz), buf, bb, hh)
      %et : strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{_}], M4.aft(tail, stack))
      strm_one(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, Pull.EStr{Lex.text(buf)}, M4.aft(tail, stack),
        next_fin(SCon{'"', xx}, stack, False{}, (Pull.SEv{Pull.EStr{Lex.text(buf)}}, M4.aft(tail, stack)),
        Equal.trans(Pull.Out, Pull.next.go(4n, SCon{'"', xx}, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, False{},
          False{}}),
          Pull.next.go(4n, SCon{'"', tail}, Pull.S{Pull.MCopy{buf}, stack, Pull.GNext{}, False{}, False{}}),
            Pull.Fin{(Pull.SEv{Pull.EStr{Lex.text(buf)}}, M4.aft(tail, stack))}, e0, sp_v(Pull.POwn{Lex.text(buf)},
                tail,
            stack, h_v, 3n))))
    case Pull.MIdle{}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{Lex.text(bb)}], M4.aft(tail, stack)),
        hh)
    case Pull.MWord{a1, a2, a3}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{Lex.text(bb)}], M4.aft(tail, stack)),
        hh)
    case Pull.MEsc{a1}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{Lex.text(bb)}], M4.aft(tail, stack)),
        hh)
    case Pull.MUni{a1, a2, a3}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{Lex.text(bb)}], M4.aft(tail, stack)),
        hh)
    case Pull.MHi{a1, a2}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{Lex.text(bb)}], M4.aft(tail, stack)),
        hh)
    case Pull.MHiEsc{a1, a2}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{Lex.text(bb)}], M4.aft(tail, stack)),
        hh)
    case Pull.MLo{a1, a2, a3, a4}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{Lex.text(bb)}], M4.aft(tail, stack)),
        hh)
    case Pull.MSkStr{}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{Lex.text(bb)}], M4.aft(tail, stack)),
        hh)
    case Pull.MSkEsc{}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{Lex.text(bb)}], M4.aft(tail, stack)),
        hh)
    case Pull.MSkUni{a1, a2}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{Lex.text(bb)}], M4.aft(tail, stack)),
        hh)
    case Pull.MSkHi{a1}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{Lex.text(bb)}], M4.aft(tail, stack)),
        hh)
    case Pull.MSkHiEsc{a1}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{Lex.text(bb)}], M4.aft(tail, stack)),
        hh)
    case Pull.MSkLo{a1, a2, a3}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{Lex.text(bb)}], M4.aft(tail, stack)),
        hh)
    case Pull.MDone{a1, a2}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{Lex.text(bb)}], M4.aft(tail, stack)),
        hh)
    case Pull.MRest{a1}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{Lex.text(bb)}], M4.aft(tail, stack)),
        hh)
    case Pull.MJump{a1, a2}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{Lex.text(bb)}], M4.aft(tail, stack)),
        hh)

# a string's closing quote, from whatever string mode holds its characters
law str_fin_k:
  for +mm: Pull.Mode
  for +bb: List<&2, Char>
  for +tail: String
  for +fr: Bool
  for +frames: List<&2, Pull.Frame>
  for +xx: String
  for e0: {Pull.next.go(4n, SCon{'"', xx}, Pull.S{Pull.MIdle{}, Pull.FObj{Pull.SKey{}, fr} <> frames, Pull.GNext{},
    False{}, False{}})
    == Pull.next.go(4n, SCon{'"', tail}, Pull.S{mm, Pull.FObj{Pull.SKey{}, fr} <> frames, Pull.GNext{}, False{},
      False{}}) : Pull.Out}
  for hh: M15.hold(mm, SCon{'"', tail}, bb)
  strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}}, [D1.VKey{Lex.text(bb)}],
    Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}})

def str_fin_k(mm, bb, tail, fr, frames, xx, e0, hh):
  match mm:
    case Pull.MQuote{}:
      (e_b, _e_s) = hh
      es = Equal.sym(List<&2, Char>, bb, [], e_b)
      %es : strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
        [D1.VKey{Lex.text(_)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}})
      strm_one(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}}, Pull.EKeyS{"", 0},
        Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}, next_fin(SCon{'"', xx},
        Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, (Pull.SEv{Pull.EKeyS{"", 0}}, Pull.Cur{tail,
        Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}),
        Equal.trans(Pull.Out, Pull.next.go(4n, SCon{'"', xx}, Pull.S{Pull.MIdle{}, Pull.FObj{Pull.SKey{},
          fr} <> frames, Pull.GNext{}, False{}, False{}}),
          Pull.next.go(4n, SCon{'"', tail}, Pull.S{Pull.MQuote{}, Pull.FObj{Pull.SKey{}, fr} <> frames, Pull.GNext{},
            False{}, False{}}), Pull.Fin{(Pull.SEv{Pull.EKeyS{"", 0}}, Pull.Cur{tail, Pull.FObj{Pull.SCol{},
            False{}} <> frames, False{}, False{}})}, e0, go_rest(3n, tail, Pull.SEv{Pull.EKeyS{"", 0}},
            Pull.FObj{Pull.SCol{}, False{}} <> frames, Pull.GNext{}, False{}, False{}))))
    case Pull.MSpan{+cut, +nn}:
      (_e_d, (e_r, _e_s)) = hh
      et = Equal.trans(String, D1.take(cut, U32.to_nat(nn)), V.span.str(cut, nn, U32.is_zero(nn)), Lex.text(bb),
        Equal.sym(String, V.span.str(cut, nn, U32.is_zero(nn)), D1.take(cut, U32.to_nat(nn)), M16.span_take(cut, nn)),
        Equal.trans(String, V.span.str(cut, nn, U32.is_zero(nn)), Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn),
          [])),
          Lex.text(bb), Equal.sym(String, Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])),
          V.span.str(cut, nn, U32.is_zero(nn)), M2.text_span(cut, nn, U32.is_zero(nn))),
          Equal.cong(List<&2, Char>, String, zz => Lex.text(zz), Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), bb,
            e_r)))
      %et : strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}}, [D1.VKey{_}],
        Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}})
      strm_one(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}}, Pull.EKeyS{cut, nn},
        Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}, next_fin(SCon{'"', xx},
        Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, (Pull.SEv{Pull.EKeyS{cut, nn}}, Pull.Cur{tail,
        Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}),
        Equal.trans(Pull.Out, Pull.next.go(4n, SCon{'"', xx}, Pull.S{Pull.MIdle{}, Pull.FObj{Pull.SKey{},
          fr} <> frames, Pull.GNext{}, False{}, False{}}),
          Pull.next.go(4n, SCon{'"', tail}, Pull.S{Pull.MSpan{cut, nn}, Pull.FObj{Pull.SKey{}, fr} <> frames,
            Pull.GNext{}, False{}, False{}}), Pull.Fin{(Pull.SEv{Pull.EKeyS{cut, nn}}, Pull.Cur{tail,
            Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}})}, e0, go_rest(3n, tail,
            Pull.SEv{Pull.EKeyS{cut, nn}}, Pull.FObj{Pull.SCol{}, False{}} <> frames, Pull.GNext{}, False{}, False{}))))
    case Pull.MCopy{+buf}:
      et = Equal.cong(List<&2, Char>, String, zz => Lex.text(zz), buf, bb, hh)
      %et : strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}}, [D1.VKey{_}],
        Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}})
      strm_one(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
        Pull.EKey{Lex.text(buf)}, Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}},
        next_fin(SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, (Pull.SEv{Pull.EKey{Lex.text(buf)}},
        Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}),
        Equal.trans(Pull.Out, Pull.next.go(4n, SCon{'"', xx}, Pull.S{Pull.MIdle{}, Pull.FObj{Pull.SKey{},
          fr} <> frames, Pull.GNext{}, False{}, False{}}),
          Pull.next.go(4n, SCon{'"', tail}, Pull.S{Pull.MCopy{buf}, Pull.FObj{Pull.SKey{}, fr} <> frames, Pull.GNext{},
            False{}, False{}}), Pull.Fin{(Pull.SEv{Pull.EKey{Lex.text(buf)}}, Pull.Cur{tail, Pull.FObj{Pull.SCol{},
            False{}} <> frames, False{}, False{}})}, e0, M8.go_done(3n, tail, Pull.SEv{Pull.EKey{Lex.text(buf)}}, tail,
            Pull.FObj{Pull.SCol{}, False{}} <> frames, Pull.GNext{}, False{}, False{}))))
    case Pull.MIdle{}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
        [D1.VKey{Lex.text(bb)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}), hh)
    case Pull.MWord{a1, a2, a3}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
        [D1.VKey{Lex.text(bb)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}), hh)
    case Pull.MEsc{a1}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
        [D1.VKey{Lex.text(bb)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}), hh)
    case Pull.MUni{a1, a2, a3}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
        [D1.VKey{Lex.text(bb)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}), hh)
    case Pull.MHi{a1, a2}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
        [D1.VKey{Lex.text(bb)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}), hh)
    case Pull.MHiEsc{a1, a2}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
        [D1.VKey{Lex.text(bb)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}), hh)
    case Pull.MLo{a1, a2, a3, a4}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
        [D1.VKey{Lex.text(bb)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}), hh)
    case Pull.MSkStr{}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
        [D1.VKey{Lex.text(bb)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}), hh)
    case Pull.MSkEsc{}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
        [D1.VKey{Lex.text(bb)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}), hh)
    case Pull.MSkUni{a1, a2}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
        [D1.VKey{Lex.text(bb)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}), hh)
    case Pull.MSkHi{a1}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
        [D1.VKey{Lex.text(bb)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}), hh)
    case Pull.MSkHiEsc{a1}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
        [D1.VKey{Lex.text(bb)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}), hh)
    case Pull.MSkLo{a1, a2, a3}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
        [D1.VKey{Lex.text(bb)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}), hh)
    case Pull.MDone{a1, a2}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
        [D1.VKey{Lex.text(bb)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}), hh)
    case Pull.MRest{a1}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
        [D1.VKey{Lex.text(bb)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}), hh)
    case Pull.MJump{a1, a2}:
      Empty.absurd(strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
        [D1.VKey{Lex.text(bb)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}}), hh)

# a string where a value may go: its opening quote
law open_str_v:
  for +xx: String
  for +stack: List<&2, Pull.Frame>
  for h_v: {Pull.expect.val.go(stack) == True{} : Bool}
  {Pull.next.go(4n, SCon{'"', xx}, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, False{}, False{}})
    == Pull.next.go(4n, xx, Pull.S{Pull.MQuote{}, stack, Pull.GNext{}, False{}, False{}}) : Pull.Out}

def open_str_v(xx, stack, h_v):
  es = Equal.sym(Bool, Pull.expect.str.go(stack), True{}, val_str(stack, h_v))
  %es : {Pull.next.go(4n, xx, Pull.look.quote(stack, Pull.GNext{}, False{}, _))
    == Pull.next.go(4n, xx, Pull.S{Pull.MQuote{}, stack, Pull.GNext{}, False{}, False{}}) : Pull.Out}
  {==}

# a string where a value may go, once its pieces' walk is in hand
law next_str_v.go:
  for +ps: List<&2, D2.Piece>
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +h_v: {Pull.expect.val.go(stack) == True{} : Bool}
  for pg: pcs_ty(ps, Pull.MQuote{}, [], SCon{'"', tail}, stack, False{}, 3n)
  strm(Pull.Cur{SCon{'"', M1.sp(ps, SCon{'"', tail})}, stack, False{}, False{}}, [D1.VStr{D2.spelled(ps)}],
    M4.aft(tail, stack))

def next_str_v.go(ps, tail, stack, h_v, pg):
  (e1, hh) = pg
  +xx = M1.sp(ps, SCon{'"', tail})
  +mf = psteps(ps, Pull.MQuote{}, [], SCon{'"', tail})
  et = text_pcs(ps)
  %et : strm(Pull.Cur{SCon{'"', xx}, stack, False{}, False{}}, [D1.VStr{_}], M4.aft(tail, stack))
  str_fin_v(mf, pcs(ps, []), tail, stack, h_v, xx,
    Equal.trans(Pull.Out, Pull.next.go(4n, SCon{'"', xx}, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, False{}, False{}}),
      Pull.next.go(4n, xx, Pull.S{Pull.MQuote{}, stack, Pull.GNext{}, False{}, False{}}),
      Pull.next.go(4n, SCon{'"', tail}, Pull.S{mf, stack, Pull.GNext{}, False{}, False{}}), open_str_v(xx, stack, h_v),
      e1), hh)

# the cursor reads a string where a value may go, and moves on past its
# closing quote
law next_str_v:
  for +ps: List<&2, D2.Piece>
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +h_ok: {D2.spell_ok(ps) == True{} : Bool}
  for +h_v: {Pull.expect.val.go(stack) == True{} : Bool}
  for +h_s: {D1.short(M1.sp(ps, SCon{'"', tail})) == True{} : Bool}
  strm(Pull.Cur{SCon{'"', M1.sp(ps, SCon{'"', tail})}, stack, False{}, False{}}, [D1.VStr{D2.spelled(ps)}],
    M4.aft(tail, stack))

def next_str_v(ps, tail, stack, h_ok, h_v, h_s):
  next_str_v.go(ps, tail, stack, h_v, pieces_go(ps, Pull.MQuote{}, [], SCon{'"', tail}, stack, False{}, 3n, h_ok,
    ({==}, h_s)))

# a member's name, once its pieces' walk is in hand
law next_str_k.go:
  for +ps: List<&2, D2.Piece>
  for +tail: String
  for +fr: Bool
  for +frames: List<&2, Pull.Frame>
  for pg: pcs_ty(ps, Pull.MQuote{}, [], SCon{'"', tail}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, 3n)
  strm(Pull.Cur{SCon{'"', M1.sp(ps, SCon{'"', tail})}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
    [D1.VKey{D2.spelled(ps)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}})

def next_str_k.go(ps, tail, fr, frames, pg):
  (e1, hh) = pg
  +xx = M1.sp(ps, SCon{'"', tail})
  +mf = psteps(ps, Pull.MQuote{}, [], SCon{'"', tail})
  et = text_pcs(ps)
  %et : strm(Pull.Cur{SCon{'"', xx}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}}, [D1.VKey{_}],
    Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}})
  str_fin_k(mf, pcs(ps, []), tail, fr, frames, xx, e1, hh)

# the cursor reads a member's name, and moves on past its closing quote
law next_str_k:
  for +ps: List<&2, D2.Piece>
  for +tail: String
  for +fr: Bool
  for +frames: List<&2, Pull.Frame>
  for +h_ok: {D2.spell_ok(ps) == True{} : Bool}
  for +h_s: {D1.short(M1.sp(ps, SCon{'"', tail})) == True{} : Bool}
  strm(Pull.Cur{SCon{'"', M1.sp(ps, SCon{'"', tail})}, Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, False{}},
    [D1.VKey{D2.spelled(ps)}], Pull.Cur{tail, Pull.FObj{Pull.SCol{}, False{}} <> frames, False{}, False{}})

def next_str_k(ps, tail, fr, frames, h_ok, h_s):
  next_str_k.go(ps, tail, fr, frames, pieces_go(ps, Pull.MQuote{}, [], SCon{'"', tail},
    Pull.FObj{Pull.SKey{}, fr} <> frames, False{}, 3n, h_ok, ({==}, h_s)))

# laws/CursorEventsMatchParse.bend: the cursor on a derivation's text

# the rest of a short text is short
law short_app:
  for +aa: String
  for +bb: String
  for h: {D1.short(aa ++ bb) == True{} : Bool}
  {D1.short(bb) == True{} : Bool}

def short_app(aa, bb, h):
  match aa:
    case SNil{}:
      h
    case SCon{+hd, +tl}:
      short_app(tl, bb, M2.short_tail(hd, tl ++ bb, h))

# what follows a derivation's text in a short text is short
law short_gt:
  for +gg: D2.Gv
  for +tail: String
  for h: {D1.short(M5.gt(gg, tail)) == True{} : Bool}
  {D1.short(tail) == True{} : Bool}

def short_gt(gg, tail, h):
  short_app(D2.g.text(gg), tail, Equal.trans(Bool, D1.short(D2.g.text(gg) ++ tail), D1.short(M5.gt(gg, tail)),
    True{}, Equal.cong(String, Bool, xx => D1.short(xx), D2.g.text(gg) ++ tail, M5.gt(gg, tail), M5.gt_eq(gg, tail)),
        h))

# what follows pieces in a short text is short
law short_sp:
  for +ps: List<&2, D2.Piece>
  for +tail: String
  for h: {D1.short(M1.sp(ps, tail)) == True{} : Bool}
  {D1.short(tail) == True{} : Bool}

def short_sp(ps, tail, h):
  short_app(D2.spell(ps), tail, Equal.trans(Bool, D1.short(D2.spell(ps) ++ tail), D1.short(M1.sp(ps, tail)),
    True{}, Equal.cong(String, Bool, xx => D1.short(xx), D2.spell(ps) ++ tail, M1.sp(ps, tail), M5.sp_eq(ps, tail)), h))

# whitespace in front of a text that ends a word ends a word
law stops_ws:
  for +ws: String
  for +xx: String
  for h_w: {D1.all_ws(ws) == True{} : Bool}
  for h_x: {M6.stops(xx) == True{} : Bool}
  {M6.stops(ws ++ xx) == True{} : Bool}

def stops_ws(ws, _xx, h_w, h_x):
  match ws:
    case SNil{}:
      h_x
    case SCon{Chr{+uu}, +tl}:
      ec = Equal.sym(Lex.Class, Lex.classify(Chr{uu}), Lex.CSpace{}, M8.ws_a(uu, U32.is_eq(uu, 32), {==},
        M6.and_left(D1.is_ws(Chr{uu}), D1.all_ws(tl), h_w)))
      %ec : {Bool.not(M6.is_other(_)) == True{} : Bool}
      {==}

# an array's or object's cells, then its closing bracket, end a word
law stops_ca:
  for +rr: D2.Gv
  for +tail: String
  for h_ok: {D2.g.ok(rr, D2.GKArr{}) == True{} : Bool}
  {M6.stops(M5.gt(rr, SCon{']', tail})) == True{} : Bool}

def stops_ca(rr, tail, h_ok):
  match rr:
    case D2.GWord{+w}:
      M6.no({M6.stops(M5.gt(D2.GWord{w}, SCon{']', tail})) == True{} : Bool}, h_ok)
    case D2.GStr{+ps}:
      M6.no({M6.stops(M5.gt(D2.GStr{ps}, SCon{']', tail})) == True{} : Bool}, h_ok)
    case D2.GArr0{+w0}:
      M6.no({M6.stops(M5.gt(D2.GArr0{w0}, SCon{']', tail})) == True{} : Bool}, h_ok)
    case D2.GArr{+w0, +vv, +w1, +rr}:
      M6.no({M6.stops(M5.gt(D2.GArr{w0, vv, w1, rr}, SCon{']', tail})) == True{} : Bool}, h_ok)
    case D2.GObj0{+w0}:
      M6.no({M6.stops(M5.gt(D2.GObj0{w0}, SCon{']', tail})) == True{} : Bool}, h_ok)
    case D2.GObj{+w0, +ps, +w1, +w2, +vv, +w3, +rr}:
      M6.no({M6.stops(M5.gt(D2.GObj{w0, ps, w1, w2, vv, w3, rr}, SCon{']', tail})) == True{} : Bool}, h_ok)
    case D2.GEnd{}:
      {==}
    case D2.GNext{+w2, +vv, +w1, +rr}:
      {==}
    case D2.GNextM{+w4, +ps, +w1, +w2, +vv, +w3, +rr}:
      M6.no({M6.stops(M5.gt(D2.GNextM{w4, ps, w1, w2, vv, w3, rr}, SCon{']', tail})) == True{} : Bool}, h_ok)

# an array's or object's cells, then its closing bracket, end a word
law stops_co:
  for +rr: D2.Gv
  for +tail: String
  for h_ok: {D2.g.ok(rr, D2.GKObj{}) == True{} : Bool}
  {M6.stops(M5.gt(rr, SCon{'}', tail})) == True{} : Bool}

def stops_co(rr, tail, h_ok):
  match rr:
    case D2.GWord{+w}:
      M6.no({M6.stops(M5.gt(D2.GWord{w}, SCon{'}', tail})) == True{} : Bool}, h_ok)
    case D2.GStr{+ps}:
      M6.no({M6.stops(M5.gt(D2.GStr{ps}, SCon{'}', tail})) == True{} : Bool}, h_ok)
    case D2.GArr0{+w0}:
      M6.no({M6.stops(M5.gt(D2.GArr0{w0}, SCon{'}', tail})) == True{} : Bool}, h_ok)
    case D2.GArr{+w0, +vv, +w1, +rr}:
      M6.no({M6.stops(M5.gt(D2.GArr{w0, vv, w1, rr}, SCon{'}', tail})) == True{} : Bool}, h_ok)
    case D2.GObj0{+w0}:
      M6.no({M6.stops(M5.gt(D2.GObj0{w0}, SCon{'}', tail})) == True{} : Bool}, h_ok)
    case D2.GObj{+w0, +ps, +w1, +w2, +vv, +w3, +rr}:
      M6.no({M6.stops(M5.gt(D2.GObj{w0, ps, w1, w2, vv, w3, rr}, SCon{'}', tail})) == True{} : Bool}, h_ok)
    case D2.GEnd{}:
      {==}
    case D2.GNext{+w2, +vv, +w1, +rr}:
      M6.no({M6.stops(M5.gt(D2.GNext{w2, vv, w1, rr}, SCon{'}', tail})) == True{} : Bool}, h_ok)
    case D2.GNextM{+w4, +ps, +w1, +w2, +vv, +w3, +rr}:
      {==}

# the text a derivation stands for where it stands, whitespace first for cells
def gtx(kk: D2.GK, gg: D2.Gv, w1: String, tail: String) -> String:
  match kk:
    case D2.GKVal{}:
      M5.gt(gg, tail)
    case D2.GKArr{}:
      w1 ++ M5.gt(gg, SCon{']', tail})
    case D2.GKObj{}:
      w1 ++ M5.gt(gg, SCon{'}', tail})

# what a value's cursor must satisfy: its next step is the one on the value's text
def gcond(kk: D2.GK, gg: D2.Gv, tail: String, stack: List<&2, Pull.Frame>, c0: Pull.Cur) -> Type:
  match kk:
    case D2.GKVal{}:
      {Ezjson.next(c0) == Ezjson.next(Pull.Cur{M5.gt(gg, tail), stack, False{}, False{}}) : (Pull.Ev & Pull.Cur)}
    case _:
      Unit

# what gv_go says: the events of a value, or of cells and their closing bracket
def gv_ty(
  kk: D2.GK,
  +gg: D2.Gv,
  +w1: String,
  +tail: String,
  +stack: List<&2, Pull.Frame>,
  +fr: Bool,
  +c0: Pull.Cur
) -> Type:
  match kk:
    case D2.GKVal{}:
      strm(c0, D1.events(L2.g.val(gg)), M4.aft(tail, stack))
    case D2.GKArr{}:
      strm(Pull.Cur{w1 ++ M5.gt(gg, SCon{']', tail}), Pull.FArr{Pull.SCom{}, fr} <> stack, False{}, False{}},
        List.append(&2, D1.Evt, D1.events(L2.g.val(gg)), [D1.VEndArr{}]), M4.aft(tail, stack))
    case D2.GKObj{}:
      strm(Pull.Cur{w1 ++ M5.gt(gg, SCon{'}', tail}), Pull.FObj{Pull.SCom{}, fr} <> stack, False{}, False{}},
        List.append(&2, D1.Evt, D1.events(L2.g.val(gg)), [D1.VEndObj{}]), M4.aft(tail, stack))

# the cursor's events on a derivation's text: a value's events, or cells'
# events and the closing bracket's, where the cursor starts at the text or at
# a step that is the text's
law gv_go:
  for +gg: D2.Gv
  for +kk: D2.GK
  for +w1: String
  for +tail: String
  for +stack: List<&2, Pull.Frame>
  for +fr: Bool
  for +c0: Pull.Cur
  for +h_ok: {D2.g.ok(gg, kk) == True{} : Bool}
  for +h_w: {D1.all_ws(w1) == True{} : Bool}
  for +h_v: {Pull.expect.val.go(stack) == True{} : Bool}
  for +h_t: {M6.stops(tail) == True{} : Bool}
  for +h_s: {D1.short(gtx(kk, gg, w1, tail)) == True{} : Bool}
  for h_c: gcond(kk, gg, tail, stack, c0)
  gv_ty(kk, gg, w1, tail, stack, fr, c0)

def gv_go(gg, kk, w1, tail, stack, fr, c0, h_ok, h_w, h_v, h_t, h_s, h_c):
  match gg kk:
    case D2.GWord{+xw} D2.GKVal{}:
      next_word(xw, tail, stack, h_ok, h_t, h_v, h_s, c0, h_c)
    case D2.GWord{+xw} D2.GKArr{}:
      M6.no(gv_ty(D2.GKArr{}, D2.GWord{xw}, w1, tail, stack, fr, c0), h_ok)
    case D2.GWord{+xw} D2.GKObj{}:
      M6.no(gv_ty(D2.GKObj{}, D2.GWord{xw}, w1, tail, stack, fr, c0), h_ok)
    case D2.GStr{+xps} D2.GKVal{}:
      strm_same(c0, Pull.Cur{M5.gt(D2.GStr{xps}, tail), stack, False{}, False{}}, D1.VStr{D2.spelled(xps)}, [],
        M4.aft(tail, stack), h_c, next_str_v(xps, tail, stack, h_ok, h_v, M2.short_tail('"', M1.sp(xps, SCon{'"',
            tail}), h_s)))
    case D2.GStr{+xps} D2.GKArr{}:
      M6.no(gv_ty(D2.GKArr{}, D2.GStr{xps}, w1, tail, stack, fr, c0), h_ok)
    case D2.GStr{+xps} D2.GKObj{}:
      M6.no(gv_ty(D2.GKObj{}, D2.GStr{xps}, w1, tail, stack, fr, c0), h_ok)
    case D2.GArr0{+xw0} D2.GKVal{}:
      strm_cons(c0, Pull.EBeginArr{}, Pull.Cur{xw0 ++ SCon{']', tail}, Pull.FArr{Pull.SVal{}, True{}} <> stack,
        False{}, False{}}, [D1.view(Pull.EEndArr{})], M4.aft(tail, stack),
        Equal.trans((Pull.Ev & Pull.Cur), Ezjson.next(c0), Ezjson.next(Pull.Cur{M5.gt(D2.GArr0{xw0}, tail), stack,
          False{},
          False{}}), (Pull.EBeginArr{}, Pull.Cur{xw0 ++ SCon{']', tail}, Pull.FArr{Pull.SVal{}, True{}} <> stack,
            False{}, False{}}), h_c, next_oarr(xw0 ++ SCon{']', tail}, stack, h_v)),
        strm_one(Pull.Cur{xw0 ++ SCon{']', tail}, Pull.FArr{Pull.SVal{}, True{}} <> stack, False{}, False{}},
          Pull.EEndArr{}, M4.aft(tail, stack), Equal.trans((Pull.Ev & Pull.Cur), Ezjson.next(Pull.Cur{xw0 ++ SCon{']',
          tail}, Pull.FArr{Pull.SVal{}, True{}} <> stack, False{}, False{}}),
          Ezjson.next(Pull.Cur{SCon{']', tail}, Pull.FArr{Pull.SVal{}, True{}} <> stack, False{}, False{}}),
            (Pull.EEndArr{}, M4.aft(tail, stack)),
          next_ws(xw0, SCon{']', tail}, Pull.FArr{Pull.SVal{}, True{}} <> stack, False{}, h_ok), next_carr0(tail,
            stack, h_v))))
    case D2.GArr0{+xw0} D2.GKArr{}:
      M6.no(gv_ty(D2.GKArr{}, D2.GArr0{xw0}, w1, tail, stack, fr, c0), h_ok)
    case D2.GArr0{+xw0} D2.GKObj{}:
      M6.no(gv_ty(D2.GKObj{}, D2.GArr0{xw0}, w1, tail, stack, fr, c0), h_ok)
    case D2.GArr{+xw0, +xvv, +xw1, +xrr} D2.GKVal{}:
      +hw0 = M6.and_left(D1.all_ws(xw0), Bool.and(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw1),
        D2.g.ok(xrr, D2.GKArr{}))), h_ok)
      +r0 = M6.and_right(D1.all_ws(xw0), Bool.and(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw1),
        D2.g.ok(xrr, D2.GKArr{}))), h_ok)
      +hvv = M6.and_left(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw1), D2.g.ok(xrr, D2.GKArr{})), r0)
      +r1 = M6.and_right(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw1), D2.g.ok(xrr, D2.GKArr{})), r0)
      +hw1 = M6.and_left(D1.all_ws(xw1), D2.g.ok(xrr, D2.GKArr{}), r1)
      +hrr = M6.and_right(D1.all_ws(xw1), D2.g.ok(xrr, D2.GKArr{}), r1)
      +sv = short_app(xw0, M5.gt(xvv, xw1 ++ M5.gt(xrr, SCon{']', tail})), M2.short_tail('[', xw0 ++ M5.gt(xvv,
          xw1 ++ M5.gt(xrr,
        SCon{']', tail})), h_s))
      ea = Equal.sym(List<&2, D1.Evt>, List.append(&2, D1.Evt, List.append(&2, D1.Evt,
        D1.events(L2.g.val(xvv)), D1.events(L2.g.val(xrr))), [D1.VEndArr{}]), List.append(&2, D1.Evt,
        D1.events(L2.g.val(xvv)), List.append(&2, D1.Evt, D1.events(L2.g.val(xrr)), [D1.VEndArr{}])),
        eapp_assoc(D1.events(L2.g.val(xvv)), D1.events(L2.g.val(xrr)), [D1.VEndArr{}]))
      %ea : strm(c0, D1.VBeginArr{} <> _, M4.aft(tail, stack))
      strm_cons(c0, Pull.EBeginArr{}, Pull.Cur{xw0 ++ M5.gt(xvv, xw1 ++ M5.gt(xrr, SCon{']', tail})),
          Pull.FArr{Pull.SVal{},
        True{}} <> stack, False{}, False{}}, List.append(&2, D1.Evt, D1.events(L2.g.val(xvv)), List.append(&2,
        D1.Evt, D1.events(L2.g.val(xrr)), [D1.VEndArr{}])), M4.aft(tail, stack),
        Equal.trans((Pull.Ev & Pull.Cur), Ezjson.next(c0), Ezjson.next(Pull.Cur{M5.gt(D2.GArr{xw0, xvv, xw1, xrr},
          tail), stack, False{},
          False{}}), (Pull.EBeginArr{}, Pull.Cur{xw0 ++ M5.gt(xvv, xw1 ++ M5.gt(xrr, SCon{']', tail})),
            Pull.FArr{Pull.SVal{}, True{}} <> stack, False{}, False{}}), h_c, next_oarr(xw0 ++ M5.gt(xvv,
                xw1 ++ M5.gt(xrr,
            SCon{']', tail})), stack, h_v)),
        strm_app(Pull.Cur{xw0 ++ M5.gt(xvv, xw1 ++ M5.gt(xrr, SCon{']', tail})), Pull.FArr{Pull.SVal{},
            True{}} <> stack,
          False{}, False{}}, D1.events(L2.g.val(xvv)), Pull.Cur{xw1 ++ M5.gt(xrr, SCon{']', tail}),
          Pull.FArr{Pull.SCom{}, False{}} <> stack, False{}, False{}}, List.append(&2, D1.Evt,
          D1.events(L2.g.val(xrr)), [D1.VEndArr{}]), M4.aft(tail, stack),
          gv_go(xvv, D2.GKVal{}, "", xw1 ++ M5.gt(xrr, SCon{']', tail}), Pull.FArr{Pull.SVal{}, True{}} <> stack,
            False{}, Pull.Cur{xw0 ++ M5.gt(xvv, xw1 ++ M5.gt(xrr, SCon{']', tail})), Pull.FArr{Pull.SVal{},
                True{}} <> stack,
            False{}, False{}}, hvv, {==}, {==},
            stops_ws(xw1, M5.gt(xrr, SCon{']', tail}), hw1, stops_ca(xrr, tail, hrr)), sv,
            next_ws(xw0, M5.gt(xvv, xw1 ++ M5.gt(xrr, SCon{']', tail})), Pull.FArr{Pull.SVal{}, True{}} <> stack,
                False{},
              hw0)),
          gv_go(xrr, D2.GKArr{}, xw1, tail, stack, False{}, c0, hrr, hw1, h_v, h_t, short_gt(xvv, xw1 ++ M5.gt(xrr,
            SCon{']', tail}), sv), Unit{})))
    case D2.GArr{+xw0, +xvv, +xw1, +xrr} D2.GKArr{}:
      M6.no(gv_ty(D2.GKArr{}, D2.GArr{xw0, xvv, xw1, xrr}, w1, tail, stack, fr, c0), h_ok)
    case D2.GArr{+xw0, +xvv, +xw1, +xrr} D2.GKObj{}:
      M6.no(gv_ty(D2.GKObj{}, D2.GArr{xw0, xvv, xw1, xrr}, w1, tail, stack, fr, c0), h_ok)
    case D2.GObj0{+xw0} D2.GKVal{}:
      strm_cons(c0, Pull.EBeginObj{}, Pull.Cur{xw0 ++ SCon{'}', tail}, Pull.FObj{Pull.SKey{}, True{}} <> stack,
        False{}, False{}}, [D1.view(Pull.EEndObj{})], M4.aft(tail, stack),
        Equal.trans((Pull.Ev & Pull.Cur), Ezjson.next(c0), Ezjson.next(Pull.Cur{M5.gt(D2.GObj0{xw0}, tail), stack,
          False{},
          False{}}), (Pull.EBeginObj{}, Pull.Cur{xw0 ++ SCon{'}', tail}, Pull.FObj{Pull.SKey{}, True{}} <> stack,
            False{}, False{}}), h_c, next_oobj(xw0 ++ SCon{'}', tail}, stack, h_v)),
        strm_one(Pull.Cur{xw0 ++ SCon{'}', tail}, Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, False{}},
          Pull.EEndObj{}, M4.aft(tail, stack), Equal.trans((Pull.Ev & Pull.Cur), Ezjson.next(Pull.Cur{xw0 ++ SCon{'}',
          tail}, Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, False{}}),
          Ezjson.next(Pull.Cur{SCon{'}', tail}, Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, False{}}),
            (Pull.EEndObj{}, M4.aft(tail, stack)),
          next_ws(xw0, SCon{'}', tail}, Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, h_ok), next_cobj0(tail,
            stack, h_v))))
    case D2.GObj0{+xw0} D2.GKArr{}:
      M6.no(gv_ty(D2.GKArr{}, D2.GObj0{xw0}, w1, tail, stack, fr, c0), h_ok)
    case D2.GObj0{+xw0} D2.GKObj{}:
      M6.no(gv_ty(D2.GKObj{}, D2.GObj0{xw0}, w1, tail, stack, fr, c0), h_ok)
    case D2.GObj{+xw0, +xps, +xw1, +xw2, +xvv, +xw3, +xrr} D2.GKVal{}:
      +hw0 = M6.and_left(D1.all_ws(xw0), Bool.and(D2.spell_ok(xps), Bool.and(D1.all_ws(xw1),
        Bool.and(D1.all_ws(xw2), Bool.and(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw3), D2.g.ok(xrr,
        D2.GKObj{})))))), h_ok)
      +r0 = M6.and_right(D1.all_ws(xw0), Bool.and(D2.spell_ok(xps), Bool.and(D1.all_ws(xw1),
        Bool.and(D1.all_ws(xw2), Bool.and(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw3), D2.g.ok(xrr,
        D2.GKObj{})))))), h_ok)
      +hps = M6.and_left(D2.spell_ok(xps), Bool.and(D1.all_ws(xw1), Bool.and(D1.all_ws(xw2), Bool.and(D2.g.ok(xvv,
        D2.GKVal{}), Bool.and(D1.all_ws(xw3), D2.g.ok(xrr, D2.GKObj{}))))), r0)
      +r1 = M6.and_right(D2.spell_ok(xps), Bool.and(D1.all_ws(xw1), Bool.and(D1.all_ws(xw2), Bool.and(D2.g.ok(xvv,
        D2.GKVal{}), Bool.and(D1.all_ws(xw3), D2.g.ok(xrr, D2.GKObj{}))))), r0)
      +hw1 = M6.and_left(D1.all_ws(xw1), Bool.and(D1.all_ws(xw2), Bool.and(D2.g.ok(xvv, D2.GKVal{}),
        Bool.and(D1.all_ws(xw3), D2.g.ok(xrr, D2.GKObj{})))), r1)
      +r2 = M6.and_right(D1.all_ws(xw1), Bool.and(D1.all_ws(xw2), Bool.and(D2.g.ok(xvv, D2.GKVal{}),
        Bool.and(D1.all_ws(xw3), D2.g.ok(xrr, D2.GKObj{})))), r1)
      +hw2 = M6.and_left(D1.all_ws(xw2), Bool.and(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw3),
        D2.g.ok(xrr, D2.GKObj{}))), r2)
      +r3 = M6.and_right(D1.all_ws(xw2), Bool.and(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw3),
        D2.g.ok(xrr, D2.GKObj{}))), r2)
      +hvv = M6.and_left(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw3), D2.g.ok(xrr, D2.GKObj{})), r3)
      +r4 = M6.and_right(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw3), D2.g.ok(xrr, D2.GKObj{})), r3)
      +hw3 = M6.and_left(D1.all_ws(xw3), D2.g.ok(xrr, D2.GKObj{}), r4)
      +hrr = M6.and_right(D1.all_ws(xw3), D2.g.ok(xrr, D2.GKObj{}), r4)
      +s1 = short_app(xw0, SCon{'"', M1.sp(xps, SCon{'"', xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}',
        tail}))}})}, M2.short_tail('{', xw0 ++ SCon{'"', M1.sp(xps, SCon{'"', xw1 ++ SCon{':', xw2 ++ M5.gt(xvv,
            xw3 ++ M5.gt(xrr,
        SCon{'}', tail}))}})}, h_s))
      +s2 = M2.short_tail('"', M1.sp(xps, SCon{'"', xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}',
          tail}))}}), s1)
      +sk = M2.short_tail('"', xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail}))}, short_sp(xps,
          SCon{'"',
        xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail}))}}, s2))
      +sv = short_app(xw2, M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail})), M2.short_tail(':', xw2 ++ M5.gt(xvv,
          xw3 ++ M5.gt(xrr,
        SCon{'}', tail})), short_app(xw1, SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail}))}, sk)))
      ea = Equal.sym(List<&2, D1.Evt>, List.append(&2, D1.Evt, List.append(&2, D1.Evt,
        D1.events(L2.g.val(xvv)), D1.events(L2.g.val(xrr))), [D1.VEndObj{}]), List.append(&2, D1.Evt,
        D1.events(L2.g.val(xvv)), List.append(&2, D1.Evt, D1.events(L2.g.val(xrr)), [D1.VEndObj{}])),
        eapp_assoc(D1.events(L2.g.val(xvv)), D1.events(L2.g.val(xrr)), [D1.VEndObj{}]))
      %ea : strm(c0, D1.VBeginObj{} <> D1.VKey{D2.spelled(xps)} <> _, M4.aft(tail, stack))
      strm_cons(c0, Pull.EBeginObj{}, Pull.Cur{xw0 ++ SCon{'"', M1.sp(xps, SCon{'"', xw1 ++ SCon{':', xw2 ++ M5.gt(xvv,
        xw3 ++ M5.gt(xrr, SCon{'}', tail}))}})}, Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, False{}},
        D1.VKey{D2.spelled(xps)} <> List.append(&2, D1.Evt, D1.events(L2.g.val(xvv)), List.append(&2,
        D1.Evt, D1.events(L2.g.val(xrr)), [D1.VEndObj{}])), M4.aft(tail, stack),
        Equal.trans((Pull.Ev & Pull.Cur), Ezjson.next(c0), Ezjson.next(Pull.Cur{M5.gt(D2.GObj{xw0, xps, xw1, xw2, xvv,
          xw3, xrr}, tail), stack, False{},
          False{}}), (Pull.EBeginObj{}, Pull.Cur{xw0 ++ SCon{'"', M1.sp(xps, SCon{'"', xw1 ++ SCon{':',
              xw2 ++ M5.gt(xvv,
            xw3 ++ M5.gt(xrr, SCon{'}', tail}))}})}, Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, False{}}), h_c,
            next_oobj(xw0 ++ SCon{'"', M1.sp(xps, SCon{'"', xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr,
                SCon{'}',
            tail}))}})}, stack, h_v)),
        strm_app(Pull.Cur{xw0 ++ SCon{'"', M1.sp(xps, SCon{'"', xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr,
            SCon{'}',
          tail}))}})}, Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, False{}}, [D1.VKey{D2.spelled(xps)}],
          Pull.Cur{xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail}))}, Pull.FObj{Pull.SCol{},
          False{}} <> stack, False{}, False{}}, List.append(&2, D1.Evt, D1.events(L2.g.val(xvv)), List.append(&2,
          D1.Evt, D1.events(L2.g.val(xrr)), [D1.VEndObj{}])), M4.aft(tail, stack),
          strm_same(Pull.Cur{xw0 ++ SCon{'"', M1.sp(xps, SCon{'"', xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr,
            SCon{'}', tail}))}})}, Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, False{}}, Pull.Cur{SCon{'"',
            M1.sp(xps, SCon{'"', xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail}))}})},
            Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, False{}}, D1.VKey{D2.spelled(xps)}, [],
            Pull.Cur{xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail}))}, Pull.FObj{Pull.SCol{},
            False{}} <> stack, False{}, False{}}, next_ws(xw0, SCon{'"', M1.sp(xps, SCon{'"', xw1 ++ SCon{':',
            xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail}))}})}, Pull.FObj{Pull.SKey{}, True{}} <> stack,
            False{}, hw0), next_str_k(xps, xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail}))},
                True{},
              stack, hps, s2)),
          strm_app(Pull.Cur{xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail}))},
              Pull.FObj{Pull.SCol{},
            False{}} <> stack, False{}, False{}}, D1.events(L2.g.val(xvv)), Pull.Cur{xw3 ++ M5.gt(xrr, SCon{'}',
            tail}), Pull.FObj{Pull.SCom{}, False{}} <> stack, False{}, False{}}, List.append(&2, D1.Evt,
            D1.events(L2.g.val(xrr)), [D1.VEndObj{}]), M4.aft(tail, stack),
            gv_go(xvv, D2.GKVal{}, "", xw3 ++ M5.gt(xrr, SCon{'}', tail}), Pull.FObj{Pull.SVal{}, False{}} <> stack,
              False{}, Pull.Cur{xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail}))},
              Pull.FObj{Pull.SCol{}, False{}} <> stack, False{}, False{}}, hvv, {==},
              {==}, stops_ws(xw3, M5.gt(xrr, SCon{'}', tail}), hw3, stops_co(xrr, tail, hrr)), sv,
              next_colon(xw1, xw2, M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail})), False{}, stack, hw1, hw2)),
            gv_go(xrr, D2.GKObj{}, xw3, tail, stack, False{}, c0, hrr, hw3, h_v, h_t, short_gt(xvv, xw3 ++ M5.gt(xrr,
              SCon{'}', tail}), sv),
              Unit{}))))
    case D2.GObj{+xw0, +xps, +xw1, +xw2, +xvv, +xw3, +xrr} D2.GKArr{}:
      M6.no(gv_ty(D2.GKArr{}, D2.GObj{xw0, xps, xw1, xw2, xvv, xw3, xrr}, w1, tail, stack, fr, c0), h_ok)
    case D2.GObj{+xw0, +xps, +xw1, +xw2, +xvv, +xw3, +xrr} D2.GKObj{}:
      M6.no(gv_ty(D2.GKObj{}, D2.GObj{xw0, xps, xw1, xw2, xvv, xw3, xrr}, w1, tail, stack, fr, c0), h_ok)
    case D2.GEnd{} D2.GKVal{}:
      M6.no(gv_ty(D2.GKVal{}, D2.GEnd{}, w1, tail, stack, fr, c0), h_ok)
    case D2.GEnd{} D2.GKArr{}:
      strm_one(Pull.Cur{w1 ++ SCon{']', tail}, Pull.FArr{Pull.SCom{}, fr} <> stack, False{}, False{}}, Pull.EEndArr{},
        M4.aft(tail, stack),
        Equal.trans((Pull.Ev & Pull.Cur), Ezjson.next(Pull.Cur{w1 ++ SCon{']', tail}, Pull.FArr{Pull.SCom{},
          fr} <> stack, False{},
          False{}}), Ezjson.next(Pull.Cur{SCon{']', tail}, Pull.FArr{Pull.SCom{}, fr} <> stack, False{}, False{}}),
            (Pull.EEndArr{}, M4.aft(tail, stack)),
          next_ws(w1, SCon{']', tail}, Pull.FArr{Pull.SCom{}, fr} <> stack, False{}, h_w), next_carr(tail, fr, stack,
            h_v)))
    case D2.GEnd{} D2.GKObj{}:
      strm_one(Pull.Cur{w1 ++ SCon{'}', tail}, Pull.FObj{Pull.SCom{}, fr} <> stack, False{}, False{}}, Pull.EEndObj{},
        M4.aft(tail, stack),
        Equal.trans((Pull.Ev & Pull.Cur), Ezjson.next(Pull.Cur{w1 ++ SCon{'}', tail}, Pull.FObj{Pull.SCom{},
          fr} <> stack, False{},
          False{}}), Ezjson.next(Pull.Cur{SCon{'}', tail}, Pull.FObj{Pull.SCom{}, fr} <> stack, False{}, False{}}),
            (Pull.EEndObj{}, M4.aft(tail, stack)),
          next_ws(w1, SCon{'}', tail}, Pull.FObj{Pull.SCom{}, fr} <> stack, False{}, h_w), next_cobj(tail, fr, stack,
            h_v)))
    case D2.GNext{+xw2, +xvv, +xw1, +xrr} D2.GKVal{}:
      M6.no(gv_ty(D2.GKVal{}, D2.GNext{xw2, xvv, xw1, xrr}, w1, tail, stack, fr, c0), h_ok)
    case D2.GNext{+xw2, +xvv, +xw1, +xrr} D2.GKArr{}:
      +hw2 = M6.and_left(D1.all_ws(xw2), Bool.and(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw1),
        D2.g.ok(xrr, D2.GKArr{}))), h_ok)
      +r0 = M6.and_right(D1.all_ws(xw2), Bool.and(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw1),
        D2.g.ok(xrr, D2.GKArr{}))), h_ok)
      +hvv = M6.and_left(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw1), D2.g.ok(xrr, D2.GKArr{})), r0)
      +r1 = M6.and_right(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw1), D2.g.ok(xrr, D2.GKArr{})), r0)
      +hw1 = M6.and_left(D1.all_ws(xw1), D2.g.ok(xrr, D2.GKArr{}), r1)
      +hrr = M6.and_right(D1.all_ws(xw1), D2.g.ok(xrr, D2.GKArr{}), r1)
      +sv = short_app(xw2, M5.gt(xvv, xw1 ++ M5.gt(xrr, SCon{']', tail})), M2.short_tail(',', xw2 ++ M5.gt(xvv,
          xw1 ++ M5.gt(xrr,
        SCon{']', tail})), short_app(w1, SCon{',', xw2 ++ M5.gt(xvv, xw1 ++ M5.gt(xrr, SCon{']', tail}))}, h_s)))
      ea = Equal.sym(List<&2, D1.Evt>, List.append(&2, D1.Evt, List.append(&2, D1.Evt,
        D1.events(L2.g.val(xvv)), D1.events(L2.g.val(xrr))), [D1.VEndArr{}]), List.append(&2, D1.Evt,
        D1.events(L2.g.val(xvv)), List.append(&2, D1.Evt, D1.events(L2.g.val(xrr)), [D1.VEndArr{}])),
        eapp_assoc(D1.events(L2.g.val(xvv)), D1.events(L2.g.val(xrr)), [D1.VEndArr{}]))
      %ea : strm(Pull.Cur{w1 ++ SCon{',', xw2 ++ M5.gt(xvv, xw1 ++ M5.gt(xrr, SCon{']', tail}))}, Pull.FArr{Pull.SCom{},
        fr} <> stack, False{}, False{}}, _, M4.aft(tail, stack))
      strm_app(Pull.Cur{w1 ++ SCon{',', xw2 ++ M5.gt(xvv, xw1 ++ M5.gt(xrr, SCon{']', tail}))}, Pull.FArr{Pull.SCom{},
        fr} <> stack, False{}, False{}}, D1.events(L2.g.val(xvv)), Pull.Cur{xw1 ++ M5.gt(xrr, SCon{']', tail}),
        Pull.FArr{Pull.SCom{}, False{}} <> stack, False{}, False{}}, List.append(&2, D1.Evt,
        D1.events(L2.g.val(xrr)), [D1.VEndArr{}]), M4.aft(tail, stack),
        gv_go(xvv, D2.GKVal{}, "", xw1 ++ M5.gt(xrr, SCon{']', tail}), Pull.FArr{Pull.SVal{}, False{}} <> stack,
          False{}, Pull.Cur{w1 ++ SCon{',', xw2 ++ M5.gt(xvv, xw1 ++ M5.gt(xrr, SCon{']', tail}))},
              Pull.FArr{Pull.SCom{},
          fr} <> stack, False{}, False{}}, hvv, {==}, {==},
          stops_ws(xw1, M5.gt(xrr, SCon{']', tail}), hw1, stops_ca(xrr, tail, hrr)), sv,
          next_comma_arr(w1, xw2, M5.gt(xvv, xw1 ++ M5.gt(xrr, SCon{']', tail})), fr, stack, h_w, hw2)),
        gv_go(xrr, D2.GKArr{}, xw1, tail, stack, False{}, c0, hrr, hw1, h_v, h_t, short_gt(xvv, xw1 ++ M5.gt(xrr,
          SCon{']', tail}), sv), Unit{}))
    case D2.GNext{+xw2, +xvv, +xw1, +xrr} D2.GKObj{}:
      M6.no(gv_ty(D2.GKObj{}, D2.GNext{xw2, xvv, xw1, xrr}, w1, tail, stack, fr, c0), h_ok)
    case D2.GNextM{+xw4, +xps, +xw1, +xw2, +xvv, +xw3, +xrr} D2.GKVal{}:
      M6.no(gv_ty(D2.GKVal{}, D2.GNextM{xw4, xps, xw1, xw2, xvv, xw3, xrr}, w1, tail, stack, fr, c0), h_ok)
    case D2.GNextM{+xw4, +xps, +xw1, +xw2, +xvv, +xw3, +xrr} D2.GKArr{}:
      M6.no(gv_ty(D2.GKArr{}, D2.GNextM{xw4, xps, xw1, xw2, xvv, xw3, xrr}, w1, tail, stack, fr, c0), h_ok)
    case D2.GNextM{+xw4, +xps, +xw1, +xw2, +xvv, +xw3, +xrr} D2.GKObj{}:
      +hw4 = M6.and_left(D1.all_ws(xw4), Bool.and(D2.spell_ok(xps), Bool.and(D1.all_ws(xw1),
        Bool.and(D1.all_ws(xw2), Bool.and(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw3), D2.g.ok(xrr,
        D2.GKObj{})))))), h_ok)
      +r0 = M6.and_right(D1.all_ws(xw4), Bool.and(D2.spell_ok(xps), Bool.and(D1.all_ws(xw1),
        Bool.and(D1.all_ws(xw2), Bool.and(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw3), D2.g.ok(xrr,
        D2.GKObj{})))))), h_ok)
      +hps = M6.and_left(D2.spell_ok(xps), Bool.and(D1.all_ws(xw1), Bool.and(D1.all_ws(xw2), Bool.and(D2.g.ok(xvv,
        D2.GKVal{}), Bool.and(D1.all_ws(xw3), D2.g.ok(xrr, D2.GKObj{}))))), r0)
      +r1 = M6.and_right(D2.spell_ok(xps), Bool.and(D1.all_ws(xw1), Bool.and(D1.all_ws(xw2), Bool.and(D2.g.ok(xvv,
        D2.GKVal{}), Bool.and(D1.all_ws(xw3), D2.g.ok(xrr, D2.GKObj{}))))), r0)
      +hw1 = M6.and_left(D1.all_ws(xw1), Bool.and(D1.all_ws(xw2), Bool.and(D2.g.ok(xvv, D2.GKVal{}),
        Bool.and(D1.all_ws(xw3), D2.g.ok(xrr, D2.GKObj{})))), r1)
      +r2 = M6.and_right(D1.all_ws(xw1), Bool.and(D1.all_ws(xw2), Bool.and(D2.g.ok(xvv, D2.GKVal{}),
        Bool.and(D1.all_ws(xw3), D2.g.ok(xrr, D2.GKObj{})))), r1)
      +hw2 = M6.and_left(D1.all_ws(xw2), Bool.and(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw3),
        D2.g.ok(xrr, D2.GKObj{}))), r2)
      +r3 = M6.and_right(D1.all_ws(xw2), Bool.and(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw3),
        D2.g.ok(xrr, D2.GKObj{}))), r2)
      +hvv = M6.and_left(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw3), D2.g.ok(xrr, D2.GKObj{})), r3)
      +r4 = M6.and_right(D2.g.ok(xvv, D2.GKVal{}), Bool.and(D1.all_ws(xw3), D2.g.ok(xrr, D2.GKObj{})), r3)
      +hw3 = M6.and_left(D1.all_ws(xw3), D2.g.ok(xrr, D2.GKObj{}), r4)
      +hrr = M6.and_right(D1.all_ws(xw3), D2.g.ok(xrr, D2.GKObj{}), r4)
      +s1 = short_app(xw4, SCon{'"', M1.sp(xps, SCon{'"', xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}',
        tail}))}})}, M2.short_tail(',', xw4 ++ SCon{'"', M1.sp(xps, SCon{'"', xw1 ++ SCon{':', xw2 ++ M5.gt(xvv,
            xw3 ++ M5.gt(xrr,
        SCon{'}', tail}))}})}, short_app(w1, SCon{',', xw4 ++ SCon{'"', M1.sp(xps, SCon{'"', xw1 ++ SCon{':',
        xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail}))}})}}, h_s)))
      +s2 = M2.short_tail('"', M1.sp(xps, SCon{'"', xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}',
          tail}))}}), s1)
      +sk = M2.short_tail('"', xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail}))}, short_sp(xps,
          SCon{'"',
        xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail}))}}, s2))
      +sv = short_app(xw2, M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail})), M2.short_tail(':', xw2 ++ M5.gt(xvv,
          xw3 ++ M5.gt(xrr,
        SCon{'}', tail})), short_app(xw1, SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail}))}, sk)))
      ea = Equal.sym(List<&2, D1.Evt>, List.append(&2, D1.Evt, List.append(&2, D1.Evt,
        D1.events(L2.g.val(xvv)), D1.events(L2.g.val(xrr))), [D1.VEndObj{}]), List.append(&2, D1.Evt,
        D1.events(L2.g.val(xvv)), List.append(&2, D1.Evt, D1.events(L2.g.val(xrr)), [D1.VEndObj{}])),
        eapp_assoc(D1.events(L2.g.val(xvv)), D1.events(L2.g.val(xrr)), [D1.VEndObj{}]))
      %ea : strm(Pull.Cur{w1 ++ SCon{',', xw4 ++ SCon{'"', M1.sp(xps, SCon{'"', xw1 ++ SCon{':', xw2 ++ M5.gt(xvv,
        xw3 ++ M5.gt(xrr, SCon{'}', tail}))}})}}, Pull.FObj{Pull.SCom{}, fr} <> stack, False{}, False{}},
        D1.VKey{D2.spelled(xps)} <> _, M4.aft(tail, stack))
      strm_app(Pull.Cur{w1 ++ SCon{',', xw4 ++ SCon{'"', M1.sp(xps, SCon{'"', xw1 ++ SCon{':', xw2 ++ M5.gt(xvv,
        xw3 ++ M5.gt(xrr, SCon{'}', tail}))}})}}, Pull.FObj{Pull.SCom{}, fr} <> stack, False{}, False{}},
        [D1.VKey{D2.spelled(xps)}], Pull.Cur{xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail}))},
        Pull.FObj{Pull.SCol{}, False{}} <> stack, False{}, False{}}, List.append(&2, D1.Evt,
        D1.events(L2.g.val(xvv)), List.append(&2, D1.Evt, D1.events(L2.g.val(xrr)), [D1.VEndObj{}])),
        M4.aft(tail, stack),
        strm_same(Pull.Cur{w1 ++ SCon{',', xw4 ++ SCon{'"', M1.sp(xps, SCon{'"', xw1 ++ SCon{':', xw2 ++ M5.gt(xvv,
          xw3 ++ M5.gt(xrr, SCon{'}', tail}))}})}}, Pull.FObj{Pull.SCom{}, fr} <> stack, False{}, False{}},
          Pull.Cur{SCon{'"', M1.sp(xps, SCon{'"', xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}',
              tail}))}})},
          Pull.FObj{Pull.SKey{}, False{}} <> stack, False{}, False{}}, D1.VKey{D2.spelled(xps)}, [],
          Pull.Cur{xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail}))}, Pull.FObj{Pull.SCol{},
          False{}} <> stack, False{}, False{}},
          next_comma_obj(w1, xw4, SCon{'"', M1.sp(xps, SCon{'"', xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr,
              SCon{'}',
            tail}))}})}, fr, stack, h_w, hw4), next_str_k(xps, xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr,
                SCon{'}',
            tail}))}, False{}, stack, hps, s2)),
        strm_app(Pull.Cur{xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail}))},
            Pull.FObj{Pull.SCol{},
          False{}} <> stack, False{}, False{}}, D1.events(L2.g.val(xvv)), Pull.Cur{xw3 ++ M5.gt(xrr, SCon{'}', tail}),
          Pull.FObj{Pull.SCom{}, False{}} <> stack, False{}, False{}}, List.append(&2, D1.Evt,
          D1.events(L2.g.val(xrr)), [D1.VEndObj{}]), M4.aft(tail, stack),
          gv_go(xvv, D2.GKVal{}, "", xw3 ++ M5.gt(xrr, SCon{'}', tail}), Pull.FObj{Pull.SVal{}, False{}} <> stack,
            False{}, Pull.Cur{xw1 ++ SCon{':', xw2 ++ M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail}))},
                Pull.FObj{Pull.SCol{},
            False{}} <> stack, False{}, False{}}, hvv, {==}, {==},
            stops_ws(xw3, M5.gt(xrr, SCon{'}', tail}), hw3, stops_co(xrr, tail, hrr)), sv,
            next_colon(xw1, xw2, M5.gt(xvv, xw3 ++ M5.gt(xrr, SCon{'}', tail})), False{}, stack, hw1, hw2)),
          gv_go(xrr, D2.GKObj{}, xw3, tail, stack, False{}, c0, hrr, hw3, h_v, h_t, short_gt(xvv, xw3 ++ M5.gt(xrr,
            SCon{'}', tail}), sv),
            Unit{})))

# laws/CursorEventsMatchParse.bend: from a parse to the cursor's events

# a value's events do not see spans
law ev_own:
  for +val: V.Json
  {D1.events(D1.own(val)) == D1.events(val) : List<&2, D1.Evt>}

def ev_own(val):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{_}:
      {==}
    case V.JNum{_}:
      {==}
    case V.JStr{_}:
      {==}
    case V.JArr{+items}:
      Equal.cong(List<&2, D1.Evt>, List<&2, D1.Evt>, xx => D1.VBeginArr{} <> List.append(&2, D1.Evt, xx,
        [D1.VEndArr{}]), D1.events(D1.own(items)), D1.events(items), ev_own(items))
    case V.JObj{+pairs}:
      Equal.cong(List<&2, D1.Evt>, List<&2, D1.Evt>, xx => D1.VBeginObj{} <> List.append(&2, D1.Evt, xx,
        [D1.VEndObj{}]), D1.events(D1.own(pairs)), D1.events(pairs), ev_own(pairs))
    case V.JNil{}:
      {==}
    case V.JCons{+hd, +tl}:
      Equal.trans(List<&2, D1.Evt>, List.append(&2, D1.Evt, D1.events(D1.own(hd)), D1.events(D1.own(tl))),
        List.append(&2, D1.Evt, D1.events(hd), D1.events(D1.own(tl))),
        List.append(&2, D1.Evt, D1.events(hd), D1.events(tl)),
        Equal.cong(List<&2, D1.Evt>, List<&2, D1.Evt>, xx => List.append(&2, D1.Evt, xx,
          D1.events(D1.own(tl))), D1.events(D1.own(hd)), D1.events(hd), ev_own(hd)),
        Equal.cong(List<&2, D1.Evt>, List<&2, D1.Evt>, xx => List.append(&2, D1.Evt, D1.events(hd), xx),
          D1.events(D1.own(tl)), D1.events(tl), ev_own(tl)))
    case V.JPair{+kk, +vv, +rr}:
      Equal.trans(List<&2, D1.Evt>, D1.VKey{kk} <> List.append(&2, D1.Evt, D1.events(D1.own(vv)),
        D1.events(D1.own(rr))), D1.VKey{kk} <> List.append(&2, D1.Evt, D1.events(vv),
        D1.events(D1.own(rr))), D1.VKey{kk} <> List.append(&2, D1.Evt, D1.events(vv), D1.events(rr)),
        Equal.cong(List<&2, D1.Evt>, List<&2, D1.Evt>, xx => D1.VKey{kk} <> List.append(&2, D1.Evt, xx,
          D1.events(D1.own(rr))), D1.events(D1.own(vv)), D1.events(vv), ev_own(vv)),
        Equal.cong(List<&2, D1.Evt>, List<&2, D1.Evt>, xx => D1.VKey{kk} <> List.append(&2, D1.Evt,
          D1.events(vv), xx), D1.events(D1.own(rr)), D1.events(rr), ev_own(rr)))
    case V.JSpan{+src, +nn}:
      Equal.cong(String, List<&2, D1.Evt>, xx => [D1.VStr{xx}], V.span.str(src, nn, U32.is_zero(nn)),
        D1.take(src, U32.to_nat(nn)), M16.span_take(src, nn))
    case V.JBind{+src, +nn, +vv, +rr}:
      +ka = V.span.str(src, nn, U32.is_zero(nn))
      +kb = D1.take(src, U32.to_nat(nn))
      Equal.trans(List<&2, D1.Evt>, D1.VKey{ka} <> List.append(&2, D1.Evt, D1.events(D1.own(vv)),
        D1.events(D1.own(rr))), D1.VKey{kb} <> List.append(&2, D1.Evt, D1.events(D1.own(vv)),
        D1.events(D1.own(rr))), D1.VKey{kb} <> List.append(&2, D1.Evt, D1.events(vv), D1.events(rr)),
        Equal.cong(String, List<&2, D1.Evt>, xx => D1.VKey{xx} <> List.append(&2, D1.Evt,
          D1.events(D1.own(vv)), D1.events(D1.own(rr))), ka, kb, M16.span_take(src, nn)),
        Equal.trans(List<&2, D1.Evt>, D1.VKey{kb} <> List.append(&2, D1.Evt, D1.events(D1.own(vv)),
          D1.events(D1.own(rr))), D1.VKey{kb} <> List.append(&2, D1.Evt, D1.events(vv),
          D1.events(D1.own(rr))), D1.VKey{kb} <> List.append(&2, D1.Evt, D1.events(vv), D1.events(rr)),
          Equal.cong(List<&2, D1.Evt>, List<&2, D1.Evt>, xx => D1.VKey{kb} <> List.append(&2, D1.Evt, xx,
            D1.events(D1.own(rr))), D1.events(D1.own(vv)), D1.events(vv), ev_own(vv)),
          Equal.cong(List<&2, D1.Evt>, List<&2, D1.Evt>, xx => D1.VKey{kb} <> List.append(&2, D1.Evt,
            D1.events(vv), xx), D1.events(D1.own(rr)), D1.events(rr), ev_own(rr))))

# whitespace ends a word
law stops_allws:
  for +ws: String
  for h_w: {D1.all_ws(ws) == True{} : Bool}
  {M6.stops(ws) == True{} : Bool}

def stops_allws(ws, h_w):
  ea = M6.append_nil(ws)
  %ea : {M6.stops(_) == True{} : Bool}
  stops_ws(ws, "", h_w, {==})

# the events from a derived text's cursor: the value's, then the end
law pull_der:
  for +wa: String
  for +gg: D2.Gv
  for +wb: String
  for +h_a: {D1.all_ws(wa) == True{} : Bool}
  for +h_g: {D2.g.ok(gg, D2.GKVal{}) == True{} : Bool}
  for +h_b: {D1.all_ws(wb) == True{} : Bool}
  for +h_s: {D1.short(wa ++ M5.gt(gg, wb)) == True{} : Bool}
  {D1.pulled(1n+List.length(&2, D1.Evt, D1.events(L2.g.val(gg))), Ezjson.cursor(wa ++ M5.gt(gg, wb)))
    == List.append(&2, D1.Evt, D1.events(L2.g.val(gg)), [D1.VEnd{}]) : List<&2, D1.Evt>}

def pull_der(wa, gg, wb, h_a, h_g, h_b, h_s):
  +ee = D1.events(L2.g.val(gg))
  +ll = List.length(&2, D1.Evt, ee)
  +c0 = Ezjson.cursor(wa ++ M5.gt(gg, wb))
  ss = gv_go(gg, D2.GKVal{}, "", wb, [], False{}, c0, h_g, {==}, {==}, stops_allws(wb, h_b),
    short_app(wa, M5.gt(gg, wb), h_s), next_ws(wa, M5.gt(gg, wb), [], False{}, h_a))
  Equal.trans(List<&2, D1.Evt>, D1.pulled(1n+ll, c0), D1.pulled(Nat.add(ll, 1n), c0),
    List.append(&2, D1.Evt, ee, [D1.VEnd{}]),
    Equal.cong(Nat, List<&2, D1.Evt>, xx => D1.pulled(xx, c0), 1n+ll, Nat.add(ll, 1n),
      Equal.sym(Nat, Nat.add(ll, 1n), 1n+ll, add_one(ll))),
    Equal.trans(List<&2, D1.Evt>, D1.pulled(Nat.add(ll, 1n), c0),
      List.append(&2, D1.Evt, ee, D1.pulled(1n, Pull.Cur{wb, [], True{}, False{}})),
      List.append(&2, D1.Evt, ee, [D1.VEnd{}]), ss(1n),
      Equal.cong((Pull.Ev & Pull.Cur), List<&2, D1.Evt>, xx => List.append(&2, D1.Evt, ee,
        [D1.view(D1.ev_of(xx))]), Ezjson.next(Pull.Cur{wb, [], True{}, False{}}),
        (Pull.EEnd{}, Pull.Cur{"", [], True{}, False{}}), next_eof(wb, [], h_b))))

# the cursor's events on a text that parses, once its derivation is in hand
law pull_ev.at:
  for +txt: String
  for +jj: V.Json
  for +h_s: {D1.short(txt) == True{} : Bool}
  for +h_p: {Ezjson.parse(txt) == Some{jj} : Maybe<&2, V.Json>}
  for dd: (&wa: String -> &gg: D2.Gv -> &wb: String -> ({txt == wa ++ D2.g.text(gg) ++ wb : String}
    & {D2.derived(wa, gg, wb) == True{} : Bool}))
  {D1.pulled(1n+List.length(&2, D1.Evt, D1.events(jj)), Ezjson.cursor(txt))
    == List.append(&2, D1.Evt, D1.events(jj), [D1.VEnd{}]) : List<&2, D1.Evt>}

def pull_ev.at(txt, jj, h_s, h_p, dd):
  (+wa, (+gg, (+wb, (+e_t, +h_d)))) = dd
  +ha = M6.and_left(D1.all_ws(wa), Bool.and(D2.g.ok(gg, D2.GKVal{}), D1.all_ws(wb)), h_d)
  +rr = M6.and_right(D1.all_ws(wa), Bool.and(D2.g.ok(gg, D2.GKVal{}), D1.all_ws(wb)), h_d)
  +hg = M6.and_left(D2.g.ok(gg, D2.GKVal{}), D1.all_ws(wb), rr)
  +hb = M6.and_right(D2.g.ok(gg, D2.GKVal{}), D1.all_ws(wb), rr)
  +tx = wa ++ D2.g.text(gg) ++ wb
  +et = Equal.sym(String, txt, tx, e_t)
  +st = Equal.trans(Bool, D1.short(tx), D1.short(txt), True{}, Equal.cong(String, Bool, xx => D1.short(xx), tx,
    txt,
    et), h_s)
  +ts = L2.text_some(gg, wa, wb, hg, ha, hb, st)
  +e1 = Equal.trans(Maybe<&2, V.Json>, Some{D1.own(jj)}, D1.own_m(Ezjson.parse(tx)), Some{L2.g.val(gg)},
    Equal.sym(Maybe<&2, V.Json>, D1.own_m(Ezjson.parse(tx)), Some{D1.own(jj)}, Equal.trans(Maybe<&2, V.Json>,
      D1.own_m(Ezjson.parse(tx)), D1.own_m(Ezjson.parse(txt)), Some{D1.own(jj)},
      Equal.cong(String, Maybe<&2, V.Json>, xx => D1.own_m(Ezjson.parse(xx)), tx, txt, et),
      Equal.cong(Maybe<&2, V.Json>, Maybe<&2, V.Json>, xx => D1.own_m(xx), Ezjson.parse(txt), Some{jj}, h_p))), ts)
  +eo = Equal.cong(Maybe<&2, V.Json>, V.Json, xx => M12.unsome(xx), Some{D1.own(jj)}, Some{L2.g.val(gg)}, e1)
  evs = Equal.trans(List<&2, D1.Evt>, D1.events(L2.g.val(gg)), D1.events(D1.own(jj)), D1.events(jj),
    Equal.cong(V.Json, List<&2, D1.Evt>, xx => D1.events(xx), L2.g.val(gg), D1.own(jj),
      Equal.sym(V.Json, D1.own(jj), L2.g.val(gg), eo)), ev_own(jj))
  %evs : {D1.pulled(1n+List.length(&2, D1.Evt, _), Ezjson.cursor(txt)) == List.append(&2, D1.Evt, _,
    [D1.VEnd{}]) : List<&2, D1.Evt>}
  %et : {D1.pulled(1n+List.length(&2, D1.Evt, D1.events(L2.g.val(gg))), Ezjson.cursor(_))
    == List.append(&2, D1.Evt, D1.events(L2.g.val(gg)), [D1.VEnd{}]) : List<&2, D1.Evt>}
  eg = Equal.sym(String, D2.g.text(gg) ++ wb, M5.gt(gg, wb), M5.gt_eq(gg, wb))
  %eg : {D1.pulled(1n+List.length(&2, D1.Evt, D1.events(L2.g.val(gg))), Ezjson.cursor(wa ++ _))
    == List.append(&2, D1.Evt, D1.events(L2.g.val(gg)), [D1.VEnd{}]) : List<&2, D1.Evt>}
  pull_der(wa, gg, wb, ha, hg, hb, Equal.trans(Bool, D1.short(wa ++ M5.gt(gg, wb)), D1.short(tx), True{},
    Equal.cong(String, Bool, xx => D1.short(wa ++ xx), M5.gt(gg, wb), D2.g.text(gg) ++ wb,
      Equal.sym(String, D2.g.text(gg) ++ wb, M5.gt(gg, wb), M5.gt_eq(gg, wb))), st))

# the cursor's events on a text that parses are the value's events, then the end
law pull_ev:
  for +txt: String
  for +jj: V.Json
  for +h_s: {D1.short(txt) == True{} : Bool}
  for +h_p: {Ezjson.parse(txt) == Some{jj} : Maybe<&2, V.Json>}
  {D1.pulled(1n+List.length(&2, D1.Evt, D1.events(jj)), Ezjson.cursor(txt))
    == List.append(&2, D1.Evt, D1.events(jj), [D1.VEnd{}]) : List<&2, D1.Evt>}

def pull_ev(txt, jj, h_s, h_p):
  pull_ev.at(txt, jj, h_s, h_p, L2.text_derives(txt, h_s, Equal.cong(Maybe<&2, V.Json>, Bool,
    xx => D1.is_some(xx), Ezjson.parse(txt), Some{jj}, h_p)))

# a finished step's answer in step
def fok2(t: String, got: (Pull.Stop & Pull.Cur)) -> Type:
  match got:
    case (stop, cur):
      M4.finok(t, stop, cur)

# a walk's result in step
def oinv(t: String, oo: Pull.Out) -> Type:
  match oo:
    case Pull.Fin{got}:
      fok2(t, got)
    case Pull.More{txt, st}:
      M4.sinv(t, txt, st)

# a lexer state between tokens finishes with the tokens it stands for
law fin_eff:
  for +lx: Lex.Lex
  for hc: {M6.cm(lx, "") == True{} : Bool}
  {Lex.finish(lx) == List.reverse(&2, Lex.Tok, M6.eff(lx)) : List<&2, Lex.Tok>}

def fin_eff(lx, hc):
  match lx:
    case Lex.Lex{Lex.Idle{}, _, _}:
      {==}
    case Lex.Lex{Lex.Word{}, _, _}:
      {==}
    case Lex.Lex{Lex.Str{}, _, _}:
      M6.no({Lex.finish(lx) == List.reverse(&2, Lex.Tok, M6.eff(lx)) : List<&2, Lex.Tok>}, hc)
    case Lex.Lex{Lex.Esc{}, _, _}:
      M6.no({Lex.finish(lx) == List.reverse(&2, Lex.Tok, M6.eff(lx)) : List<&2, Lex.Tok>}, hc)
    case Lex.Lex{Lex.Uni{_, _}, _, _}:
      M6.no({Lex.finish(lx) == List.reverse(&2, Lex.Tok, M6.eff(lx)) : List<&2, Lex.Tok>}, hc)
    case Lex.Lex{Lex.Hi{_}, _, _}:
      M6.no({Lex.finish(lx) == List.reverse(&2, Lex.Tok, M6.eff(lx)) : List<&2, Lex.Tok>}, hc)
    case Lex.Lex{Lex.HiEsc{_}, _, _}:
      M6.no({Lex.finish(lx) == List.reverse(&2, Lex.Tok, M6.eff(lx)) : List<&2, Lex.Tok>}, hc)
    case Lex.Lex{Lex.Lo{_, _, _}, _, _}:
      M6.no({Lex.finish(lx) == List.reverse(&2, Lex.Tok, M6.eff(lx)) : List<&2, Lex.Tok>}, hc)
    case Lex.Lex{Lex.Bad{}, _, _}:
      M6.no({Lex.finish(lx) == List.reverse(&2, Lex.Tok, M6.eff(lx)) : List<&2, Lex.Tok>}, hc)

# a parser in step with a finished root finishes with it
law prel_fin:
  for ps: List<&2, Pull.Frame>
  for pp: Parse.P
  for h: {M6.prel(ps, True{}, pp) == True{} : Bool}
  {D1.is_some(Parse.finish(pp)) == True{} : Bool}

def prel_fin(ps, pp, h):
  match ps:
    case Nil{}:
      match pp:
        case Parse.P{True{}, _, _}:
          M6.no({D1.is_some(Parse.finish(pp)) == True{} : Bool}, h)
        case Parse.P{False{}, None{}, _}:
          M6.no({D1.is_some(Parse.finish(pp)) == True{} : Bool}, h)
        case Parse.P{False{}, Some{_}, Nil{}}:
          {==}
        case Parse.P{False{}, Some{_}, _ <> _}:
          M6.no({D1.is_some(Parse.finish(pp)) == True{} : Bool}, h)
    case _ <> _:
      match pp:
        case Parse.P{True{}, _, _}:
          M6.no({D1.is_some(Parse.finish(pp)) == True{} : Bool}, h)
        case Parse.P{False{}, None{}, _}:
          M6.no({D1.is_some(Parse.finish(pp)) == True{} : Bool}, h)
        case Parse.P{False{}, Some{_}, _}:
          M6.no({D1.is_some(Parse.finish(pp)) == True{} : Bool}, h)

# a text the lexer and a parser in step with a finished root have read to its end parses
law fin_some:
  for +tt: String
  for +lx: Lex.Lex
  for +stack: List<&2, Pull.Frame>
  for h_s: {D1.short(tt) == True{} : Bool}
  for e: M6.lx_e(tt, "", lx)
  for hc: {M6.cm(lx, "") == True{} : Bool}
  for hp: {M6.prel(stack, True{}, M6.pst(lx)) == True{} : Bool}
  {D1.is_some(Ezjson.parse(tt)) == True{} : Bool}

def fin_some(tt, lx, stack, h_s, e, hc, hp):
  +run = Lex.run(String.to_list(tt), M6.lx0())
  +ed2 = Equal.trans(List<&2, Lex.Tok>, M6.dens(Lex.tokens(tt)), M6.dens(Lex.finish(run)),
    M6.dens(List.reverse(&2, Lex.Tok, M6.eff(lx))), M2.lexers_agree(tt, h_s),
    Equal.trans(List<&2, Lex.Tok>, M6.dens(Lex.finish(run)), M6.dens(Lex.finish(lx)),
      M6.dens(List.reverse(&2, Lex.Tok, M6.eff(lx))),
      Equal.cong(Lex.Lex, List<&2, Lex.Tok>, xx => M6.dens(Lex.finish(xx)), run, lx, e),
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, xx => M6.dens(xx), Lex.finish(lx),
        List.reverse(&2, Lex.Tok, M6.eff(lx)), fin_eff(lx, hc))))
  +eo = Equal.trans(Maybe<&2, V.Json>, D1.own_m(Ezjson.parse(tt)),
    Parse.finish(M11.ownp(Parse.run(Lex.tokens(tt), M6.pp0()))), Parse.finish(M6.pst(lx)),
    M11.fin_own(Parse.run(Lex.tokens(tt), M6.pp0())),
    Equal.trans(Maybe<&2, V.Json>, Parse.finish(M11.ownp(Parse.run(Lex.tokens(tt), M6.pp0()))),
      Parse.finish(Parse.run(M6.dens(Lex.tokens(tt)), M6.pp0())), Parse.finish(M6.pst(lx)),
      Equal.cong(Parse.P, Maybe<&2, V.Json>, xx => Parse.finish(xx), M11.ownp(Parse.run(Lex.tokens(tt), M6.pp0())),
        Parse.run(M6.dens(Lex.tokens(tt)), M6.pp0()), M11.run_own(Lex.tokens(tt), M6.pp0())),
      Equal.cong(List<&2, Lex.Tok>, Maybe<&2, V.Json>, xx => Parse.finish(Parse.run(xx, M6.pp0())),
        M6.dens(Lex.tokens(tt)), M6.dens(List.reverse(&2, Lex.Tok, M6.eff(lx))), ed2)))
  Equal.trans(Bool, D1.is_some(Ezjson.parse(tt)), D1.is_some(D1.own_m(Ezjson.parse(tt))), True{},
    Equal.sym(Bool, D1.is_some(D1.own_m(Ezjson.parse(tt))), D1.is_some(Ezjson.parse(tt)),
      M6.some_own(Ezjson.parse(tt))),
    Equal.trans(Bool, D1.is_some(D1.own_m(Ezjson.parse(tt))), D1.is_some(Parse.finish(M6.pst(lx))), True{},
      Equal.cong(Maybe<&2, V.Json>, Bool, xx => D1.is_some(xx), D1.own_m(Ezjson.parse(tt)),
        Parse.finish(M6.pst(lx)), eo), prel_fin(stack, M6.pst(lx), hp)))

# where the cursor lets a value go, a parser in step lets one go
law ready_rel:
  for +stack: List<&2, Pull.Frame>
  for +qs: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +hp: {M6.prel(stack, False{}, Parse.P{False{}, root, qs}) == True{} : Bool}
  for hv: {Pull.expect.val.go(stack) == True{} : Bool}
  {Parse.step.ready(qs, root) == True{} : Bool}

def ready_rel(stack, qs, root, hp, hv):
  match stack:
    case Nil{}:
      match qs:
        case Nil{}:
          match root:
            case None{}:
              {==}
            case Some{+rv}:
              M6.no({Parse.step.ready([], Some{rv}) == True{} : Bool}, M6.and_left(M6.rrel(False{}, Some{rv}, []),
                  M6.frels([],
                []), hp))
        case +q <> +qt:
          M6.no({Parse.step.ready(q <> qt, root) == True{} : Bool}, M6.and_right(M6.rrel(False{}, root, []),
              M6.frels([], q <> qt),
            hp))
    case Pull.FArr{Pull.SVal{}, +fr} <> +st:
      match qs:
        case Nil{}:
          M6.no({Parse.step.ready([], root) == True{} : Bool}, M6.and_right(M6.rrel(False{}, root,
              Pull.FArr{Pull.SVal{},
            fr} <> st), M6.frels(Pull.FArr{Pull.SVal{}, fr} <> st, []), hp))
        case Parse.FArr{+items, Parse.SValue{}} <> +qt:
          match root:
            case None{}:
              {==}
            case Some{+rv}:
              M6.no({Parse.step.ready(Parse.FArr{items, Parse.SValue{}} <> qt, Some{rv}) == True{} : Bool},
                M6.and_left(M6.rrel(False{}, Some{rv}, Pull.FArr{Pull.SVal{}, fr} <> st),
                    M6.frels(Pull.FArr{Pull.SVal{},
                fr} <> st, Parse.FArr{items, Parse.SValue{}} <> qt), hp))
        case Parse.FArr{+items, Parse.SComma{}} <> +qt:
          M6.no({Parse.step.ready(Parse.FArr{items, Parse.SComma{}} <> qt, root) == True{} : Bool},
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, fr} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{}, fr},
            Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SKey{}} <> +qt:
          M6.no({Parse.step.ready(Parse.FArr{items, Parse.SKey{}} <> qt, root) == True{} : Bool},
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, fr} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{}, fr},
            Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SColon{}} <> +qt:
          M6.no({Parse.step.ready(Parse.FArr{items, Parse.SColon{}} <> qt, root) == True{} : Bool},
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, fr} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{}, fr},
            Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SValue{}} <> +qt:
          M6.no({Parse.step.ready(Parse.FObj{items, kk, Parse.SValue{}} <> qt, root) == True{} : Bool},
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, fr} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{}, fr},
            Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SComma{}} <> +qt:
          M6.no({Parse.step.ready(Parse.FObj{items, kk, Parse.SComma{}} <> qt, root) == True{} : Bool},
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, fr} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{}, fr},
            Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SKey{}} <> +qt:
          M6.no({Parse.step.ready(Parse.FObj{items, kk, Parse.SKey{}} <> qt, root) == True{} : Bool},
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, fr} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{}, fr},
            Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SColon{}} <> +qt:
          M6.no({Parse.step.ready(Parse.FObj{items, kk, Parse.SColon{}} <> qt, root) == True{} : Bool},
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, fr} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{}, fr},
            Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt)), hp)))
    case Pull.FArr{Pull.SCom{}, +fr} <> +st:
      M6.no({Parse.step.ready(qs, root) == True{} : Bool}, hv)
    case Pull.FArr{Pull.SKey{}, +fr} <> +st:
      M6.no({Parse.step.ready(qs, root) == True{} : Bool}, hv)
    case Pull.FArr{Pull.SCol{}, +fr} <> +st:
      M6.no({Parse.step.ready(qs, root) == True{} : Bool}, hv)
    case Pull.FObj{Pull.SVal{}, +fr} <> +st:
      match qs:
        case Nil{}:
          M6.no({Parse.step.ready([], root) == True{} : Bool}, M6.and_right(M6.rrel(False{}, root,
              Pull.FObj{Pull.SVal{},
            fr} <> st), M6.frels(Pull.FObj{Pull.SVal{}, fr} <> st, []), hp))
        case Parse.FArr{+items, Parse.SValue{}} <> +qt:
          M6.no({Parse.step.ready(Parse.FArr{items, Parse.SValue{}} <> qt, root) == True{} : Bool},
            M6.and_left(M6.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SVal{}, fr} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SVal{}, fr},
            Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SComma{}} <> +qt:
          M6.no({Parse.step.ready(Parse.FArr{items, Parse.SComma{}} <> qt, root) == True{} : Bool},
            M6.and_left(M6.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SVal{}, fr} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SVal{}, fr},
            Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SKey{}} <> +qt:
          M6.no({Parse.step.ready(Parse.FArr{items, Parse.SKey{}} <> qt, root) == True{} : Bool},
            M6.and_left(M6.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SVal{}, fr} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SVal{}, fr},
            Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SColon{}} <> +qt:
          M6.no({Parse.step.ready(Parse.FArr{items, Parse.SColon{}} <> qt, root) == True{} : Bool},
            M6.and_left(M6.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SVal{}, fr} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SVal{}, fr},
            Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SValue{}} <> +qt:
          match root:
            case None{}:
              {==}
            case Some{+rv}:
              M6.no({Parse.step.ready(Parse.FObj{items, kk, Parse.SValue{}} <> qt, Some{rv}) == True{} : Bool},
                M6.and_left(M6.rrel(False{}, Some{rv}, Pull.FObj{Pull.SVal{}, fr} <> st),
                    M6.frels(Pull.FObj{Pull.SVal{},
                fr} <> st, Parse.FObj{items, kk, Parse.SValue{}} <> qt), hp))
        case Parse.FObj{+items, +kk, Parse.SComma{}} <> +qt:
          M6.no({Parse.step.ready(Parse.FObj{items, kk, Parse.SComma{}} <> qt, root) == True{} : Bool},
            M6.and_left(M6.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SVal{}, fr} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SVal{}, fr},
            Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SKey{}} <> +qt:
          M6.no({Parse.step.ready(Parse.FObj{items, kk, Parse.SKey{}} <> qt, root) == True{} : Bool},
            M6.and_left(M6.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SVal{}, fr} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SVal{}, fr},
            Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SColon{}} <> +qt:
          M6.no({Parse.step.ready(Parse.FObj{items, kk, Parse.SColon{}} <> qt, root) == True{} : Bool},
            M6.and_left(M6.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SVal{}, fr} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SVal{}, fr},
            Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt)), hp)))
    case Pull.FObj{Pull.SCom{}, +fr} <> +st:
      M6.no({Parse.step.ready(qs, root) == True{} : Bool}, hv)
    case Pull.FObj{Pull.SKey{}, +fr} <> +st:
      M6.no({Parse.step.ready(qs, root) == True{} : Bool}, hv)
    case Pull.FObj{Pull.SCol{}, +fr} <> +st:
      M6.no({Parse.step.ready(qs, root) == True{} : Bool}, hv)

# where the cursor lets a value go, a string is a value to the parser too
law ps_put:
  for +stack: List<&2, Pull.Frame>
  for +qs: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +key: Parse.Key
  for +hp: {M6.prel(stack, False{}, Parse.P{False{}, root, qs}) == True{} : Bool}
  for hv: {Pull.expect.val.go(stack) == True{} : Bool}
  {Parse.put.str(qs, root, key, False{}) == Parse.put(qs, root, Parse.put.text(key), False{}) : Parse.P}

def ps_put(stack, qs, root, key, hp, hv):
  match stack:
    case Nil{}:
      match qs:
        case Nil{}:
          match root:
            case None{}:
              {==}
            case Some{+rv}:
              M6.no({Parse.put.str([], Some{rv}, key, False{}) == Parse.put([], Some{rv}, Parse.put.text(key),
                False{}) : Parse.P}, M6.and_left(M6.rrel(False{}, Some{rv}, []), M6.frels([], []), hp))
        case +q <> +qt:
          M6.no({Parse.put.str(q <> qt, root, key, False{}) == Parse.put(q <> qt, root, Parse.put.text(key),
            False{}) : Parse.P}, M6.and_right(M6.rrel(False{}, root, []), M6.frels([], q <> qt), hp))
    case Pull.FArr{Pull.SVal{}, +fr} <> +st:
      match qs:
        case Nil{}:
          M6.no({Parse.put.str([], root, key, False{}) == Parse.put([], root, Parse.put.text(key), False{}) : Parse.P},
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, fr} <> st), M6.frels(Pull.FArr{Pull.SVal{},
                fr} <> st,
            []), hp))
        case Parse.FArr{+items, Parse.SValue{}} <> +qt:
          match root:
            case None{}:
              {==}
            case Some{+rv}:
              M6.no({Parse.put.str(Parse.FArr{items, Parse.SValue{}} <> qt, Some{rv}, key,
                False{}) == Parse.put(Parse.FArr{items, Parse.SValue{}} <> qt, Some{rv}, Parse.put.text(key),
                False{}) : Parse.P}, M6.and_left(M6.rrel(False{}, Some{rv}, Pull.FArr{Pull.SVal{}, fr} <> st),
                M6.frels(Pull.FArr{Pull.SVal{}, fr} <> st, Parse.FArr{items, Parse.SValue{}} <> qt), hp))
        case Parse.FArr{+items, Parse.SComma{}} <> +qt:
          M6.no({Parse.put.str(Parse.FArr{items, Parse.SComma{}} <> qt, root, key,
              False{}) == Parse.put(Parse.FArr{items,
            Parse.SComma{}} <> qt, root, Parse.put.text(key), False{}) : Parse.P},
                M6.and_left(M6.frel(Pull.FArr{Pull.SVal{},
            fr}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt), M6.and_right(M6.rrel(False{}, root,
            Pull.FArr{Pull.SVal{}, fr} <> st), Bool.and(M6.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FArr{items,
            Parse.SComma{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SKey{}} <> +qt:
          M6.no({Parse.put.str(Parse.FArr{items, Parse.SKey{}} <> qt, root, key, False{}) == Parse.put(Parse.FArr{items,
            Parse.SKey{}} <> qt, root, Parse.put.text(key), False{}) : Parse.P},
                M6.and_left(M6.frel(Pull.FArr{Pull.SVal{},
            fr}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt), M6.and_right(M6.rrel(False{}, root,
                Pull.FArr{Pull.SVal{},
            fr} <> st), Bool.and(M6.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st,
                qt)),
            hp)))
        case Parse.FArr{+items, Parse.SColon{}} <> +qt:
          M6.no({Parse.put.str(Parse.FArr{items, Parse.SColon{}} <> qt, root, key,
              False{}) == Parse.put(Parse.FArr{items,
            Parse.SColon{}} <> qt, root, Parse.put.text(key), False{}) : Parse.P},
                M6.and_left(M6.frel(Pull.FArr{Pull.SVal{},
            fr}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt), M6.and_right(M6.rrel(False{}, root,
            Pull.FArr{Pull.SVal{}, fr} <> st), Bool.and(M6.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FArr{items,
            Parse.SColon{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SValue{}} <> +qt:
          M6.no({Parse.put.str(Parse.FObj{items, kk, Parse.SValue{}} <> qt, root, key,
            False{}) == Parse.put(Parse.FObj{items, kk, Parse.SValue{}} <> qt, root, Parse.put.text(key),
            False{}) : Parse.P}, M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SValue{}}),
            M6.frels(st, qt), M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, fr} <> st),
            Bool.and(M6.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt)),
                hp)))
        case Parse.FObj{+items, +kk, Parse.SComma{}} <> +qt:
          M6.no({Parse.put.str(Parse.FObj{items, kk, Parse.SComma{}} <> qt, root, key,
            False{}) == Parse.put(Parse.FObj{items, kk, Parse.SComma{}} <> qt, root, Parse.put.text(key),
            False{}) : Parse.P}, M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SComma{}}),
            M6.frels(st, qt), M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, fr} <> st),
            Bool.and(M6.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st, qt)),
                hp)))
        case Parse.FObj{+items, +kk, Parse.SKey{}} <> +qt:
          M6.no({Parse.put.str(Parse.FObj{items, kk, Parse.SKey{}} <> qt, root, key,
            False{}) == Parse.put(Parse.FObj{items, kk, Parse.SKey{}} <> qt, root, Parse.put.text(key),
            False{}) : Parse.P}, M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SKey{}}),
            M6.frels(st, qt), M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, fr} <> st),
            Bool.and(M6.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SColon{}} <> +qt:
          M6.no({Parse.put.str(Parse.FObj{items, kk, Parse.SColon{}} <> qt, root, key,
            False{}) == Parse.put(Parse.FObj{items, kk, Parse.SColon{}} <> qt, root, Parse.put.text(key),
            False{}) : Parse.P}, M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SColon{}}),
            M6.frels(st, qt), M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, fr} <> st),
            Bool.and(M6.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt)),
                hp)))
    case Pull.FArr{Pull.SCom{}, +fr} <> +st:
      M6.no({Parse.put.str(qs, root, key, False{}) == Parse.put(qs, root, Parse.put.text(key), False{}) : Parse.P}, hv)
    case Pull.FArr{Pull.SKey{}, +fr} <> +st:
      M6.no({Parse.put.str(qs, root, key, False{}) == Parse.put(qs, root, Parse.put.text(key), False{}) : Parse.P}, hv)
    case Pull.FArr{Pull.SCol{}, +fr} <> +st:
      M6.no({Parse.put.str(qs, root, key, False{}) == Parse.put(qs, root, Parse.put.text(key), False{}) : Parse.P}, hv)
    case Pull.FObj{Pull.SVal{}, +fr} <> +st:
      match qs:
        case Nil{}:
          M6.no({Parse.put.str([], root, key, False{}) == Parse.put([], root, Parse.put.text(key), False{}) : Parse.P},
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SVal{}, fr} <> st), M6.frels(Pull.FObj{Pull.SVal{},
                fr} <> st,
            []), hp))
        case Parse.FArr{+items, Parse.SValue{}} <> +qt:
          M6.no({Parse.put.str(Parse.FArr{items, Parse.SValue{}} <> qt, root, key,
              False{}) == Parse.put(Parse.FArr{items,
            Parse.SValue{}} <> qt, root, Parse.put.text(key), False{}) : Parse.P},
                M6.and_left(M6.frel(Pull.FObj{Pull.SVal{},
            fr}, Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt), M6.and_right(M6.rrel(False{}, root,
            Pull.FObj{Pull.SVal{}, fr} <> st), Bool.and(M6.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FArr{items,
            Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SComma{}} <> +qt:
          M6.no({Parse.put.str(Parse.FArr{items, Parse.SComma{}} <> qt, root, key,
              False{}) == Parse.put(Parse.FArr{items,
            Parse.SComma{}} <> qt, root, Parse.put.text(key), False{}) : Parse.P},
                M6.and_left(M6.frel(Pull.FObj{Pull.SVal{},
            fr}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt), M6.and_right(M6.rrel(False{}, root,
            Pull.FObj{Pull.SVal{}, fr} <> st), Bool.and(M6.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FArr{items,
            Parse.SComma{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SKey{}} <> +qt:
          M6.no({Parse.put.str(Parse.FArr{items, Parse.SKey{}} <> qt, root, key, False{}) == Parse.put(Parse.FArr{items,
            Parse.SKey{}} <> qt, root, Parse.put.text(key), False{}) : Parse.P},
                M6.and_left(M6.frel(Pull.FObj{Pull.SVal{},
            fr}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt), M6.and_right(M6.rrel(False{}, root,
                Pull.FObj{Pull.SVal{},
            fr} <> st), Bool.and(M6.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st,
                qt)),
            hp)))
        case Parse.FArr{+items, Parse.SColon{}} <> +qt:
          M6.no({Parse.put.str(Parse.FArr{items, Parse.SColon{}} <> qt, root, key,
              False{}) == Parse.put(Parse.FArr{items,
            Parse.SColon{}} <> qt, root, Parse.put.text(key), False{}) : Parse.P},
                M6.and_left(M6.frel(Pull.FObj{Pull.SVal{},
            fr}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt), M6.and_right(M6.rrel(False{}, root,
            Pull.FObj{Pull.SVal{}, fr} <> st), Bool.and(M6.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FArr{items,
            Parse.SColon{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SValue{}} <> +qt:
          match root:
            case None{}:
              {==}
            case Some{+rv}:
              M6.no({Parse.put.str(Parse.FObj{items, kk, Parse.SValue{}} <> qt, Some{rv}, key,
                False{}) == Parse.put(Parse.FObj{items, kk, Parse.SValue{}} <> qt, Some{rv}, Parse.put.text(key),
                False{}) : Parse.P}, M6.and_left(M6.rrel(False{}, Some{rv}, Pull.FObj{Pull.SVal{}, fr} <> st),
                M6.frels(Pull.FObj{Pull.SVal{}, fr} <> st, Parse.FObj{items, kk, Parse.SValue{}} <> qt), hp))
        case Parse.FObj{+items, +kk, Parse.SComma{}} <> +qt:
          M6.no({Parse.put.str(Parse.FObj{items, kk, Parse.SComma{}} <> qt, root, key,
            False{}) == Parse.put(Parse.FObj{items, kk, Parse.SComma{}} <> qt, root, Parse.put.text(key),
            False{}) : Parse.P}, M6.and_left(M6.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SComma{}}),
            M6.frels(st, qt), M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SVal{}, fr} <> st),
            Bool.and(M6.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st, qt)),
                hp)))
        case Parse.FObj{+items, +kk, Parse.SKey{}} <> +qt:
          M6.no({Parse.put.str(Parse.FObj{items, kk, Parse.SKey{}} <> qt, root, key,
            False{}) == Parse.put(Parse.FObj{items, kk, Parse.SKey{}} <> qt, root, Parse.put.text(key),
            False{}) : Parse.P}, M6.and_left(M6.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SKey{}}),
            M6.frels(st, qt), M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SVal{}, fr} <> st),
            Bool.and(M6.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SColon{}} <> +qt:
          M6.no({Parse.put.str(Parse.FObj{items, kk, Parse.SColon{}} <> qt, root, key,
            False{}) == Parse.put(Parse.FObj{items, kk, Parse.SColon{}} <> qt, root, Parse.put.text(key),
            False{}) : Parse.P}, M6.and_left(M6.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SColon{}}),
            M6.frels(st, qt), M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SVal{}, fr} <> st),
            Bool.and(M6.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt)),
                hp)))
    case Pull.FObj{Pull.SCom{}, +fr} <> +st:
      M6.no({Parse.put.str(qs, root, key, False{}) == Parse.put(qs, root, Parse.put.text(key), False{}) : Parse.P}, hv)
    case Pull.FObj{Pull.SKey{}, +fr} <> +st:
      M6.no({Parse.put.str(qs, root, key, False{}) == Parse.put(qs, root, Parse.put.text(key), False{}) : Parse.P}, hv)
    case Pull.FObj{Pull.SCol{}, +fr} <> +st:
      M6.no({Parse.put.str(qs, root, key, False{}) == Parse.put(qs, root, Parse.put.text(key), False{}) : Parse.P}, hv)

# a container closed: where a value may go, the cursor is past it as after a value
law cl_inv_a:
  for +tt: String
  for +tl: String
  for +fr: List<&2, Pull.Frame>
  for kk: {Pull.expect.val.go(fr) == True{} : Bool} -> M6.cinv(tt, M4.aft(tl, fr))
  M4.sinv(tt, tl, Pull.close.out(Pull.EEndArr{}, fr, Pull.GNext{}))

def cl_inv_a(_tt, _tl, fr, kk):
  match fr:
    case Nil{}:
      kk({==})
    case Pull.FArr{Pull.SVal{}, _} <> _:
      kk({==})
    case Pull.FArr{Pull.SCom{}, _} <> _:
      Unit{}
    case Pull.FArr{Pull.SKey{}, _} <> _:
      Unit{}
    case Pull.FArr{Pull.SCol{}, _} <> _:
      Unit{}
    case Pull.FObj{Pull.SVal{}, _} <> _:
      kk({==})
    case Pull.FObj{Pull.SCom{}, _} <> _:
      Unit{}
    case Pull.FObj{Pull.SKey{}, _} <> _:
      Unit{}
    case Pull.FObj{Pull.SCol{}, _} <> _:
      Unit{}

# a container closed: where a value may go, the cursor is past it as after a value
law cl_inv_o:
  for +tt: String
  for +tl: String
  for +fr: List<&2, Pull.Frame>
  for kk: {Pull.expect.val.go(fr) == True{} : Bool} -> M6.cinv(tt, M4.aft(tl, fr))
  M4.sinv(tt, tl, Pull.close.out(Pull.EEndObj{}, fr, Pull.GNext{}))

def cl_inv_o(_tt, _tl, fr, kk):
  match fr:
    case Nil{}:
      kk({==})
    case Pull.FArr{Pull.SVal{}, _} <> _:
      kk({==})
    case Pull.FArr{Pull.SCom{}, _} <> _:
      Unit{}
    case Pull.FArr{Pull.SKey{}, _} <> _:
      Unit{}
    case Pull.FArr{Pull.SCol{}, _} <> _:
      Unit{}
    case Pull.FObj{Pull.SVal{}, _} <> _:
      kk({==})
    case Pull.FObj{Pull.SCom{}, _} <> _:
      Unit{}
    case Pull.FObj{Pull.SKey{}, _} <> _:
      Unit{}
    case Pull.FObj{Pull.SCol{}, _} <> _:
      Unit{}

# an opening bracket where a value may go: the parser opens the same frame
law oa_rel:
  for +stack: List<&2, Pull.Frame>
  for +qs: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +hp: {M6.prel(stack, False{}, Parse.P{False{}, root, qs}) == True{} : Bool}
  for hv: {Pull.expect.val.go(stack) == True{} : Bool}
  {M6.prel(Pull.FArr{Pull.SVal{}, True{}} <> stack, False{}, Parse.step(Lex.TOpenArr{}, Parse.P{False{}, root,
    qs})) == True{} : Bool}

def oa_rel(stack, qs, root, hp, hv):
  match root:
    case None{}:
      rs = Equal.sym(Bool, Parse.step.ready(qs, None{}), True{}, ready_rel(stack, qs, None{}, hp, hv))
      %rs : {M6.prel(Pull.FArr{Pull.SVal{}, True{}} <> stack, False{}, Parse.step.open_arr.go(False{}, None{}, qs,
        _)) == True{} : Bool}
      hp
    case Some{+rv}:
      M6.no({M6.prel(Pull.FArr{Pull.SVal{}, True{}} <> stack, False{}, Parse.step(Lex.TOpenArr{}, Parse.P{False{},
          Some{rv},
        qs})) == True{} : Bool},
        M6.and_left(M6.rrel(False{}, Some{rv}, stack), M6.frels(stack, qs), hp))

# an opening bracket, once whether a value may go is named
law p_oarr.at:
  for +tt: String
  for +tl: String
  for +lx: Lex.Lex
  for +stack: List<&2, Pull.Frame>
  for +qs: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +h_s: {D1.short(tl) == True{} : Bool}
  for +e: M6.lx_e(tt, tl, lx)
  for +hc: {M6.cm(lx, tl) == True{} : Bool}
  for +hp: {M6.prel(stack, False{}, Parse.P{False{}, root, qs}) == True{} : Bool}
  for +eq: {M6.pst(lx) == Parse.step(Lex.TOpenArr{}, Parse.P{False{}, root, qs}) : Parse.P}
  for bv: Bool
  for +ev: {Pull.expect.val.go(stack) == bv : Bool}
  M4.sinv(tt, tl, Pull.punct.go(Lex.TOpenArr{}, stack, Pull.GNext{}, False{}))

def p_oarr.at(tt, tl, lx, stack, qs, root, h_s, e, hc, hp, eq, bv, ev):
  match bv:
    case False{}:
      es = Equal.sym(Bool, Pull.expect.val.go(stack), False{}, ev)
      %es : M4.sinv(tt, tl, Pull.punct.arr.if(stack, Pull.GNext{}, _))
      Unit{}
    case True{}:
      es = Equal.sym(Bool, Pull.expect.val.go(stack), True{}, ev)
      %es : M4.sinv(tt, tl, Pull.punct.arr.if(stack, Pull.GNext{}, _))
      (h_s, (lx, (e, (hc, Equal.trans(Bool, M6.prel(Pull.FArr{Pull.SVal{}, True{}} <> stack, False{}, M6.pst(lx)),
        M6.prel(Pull.FArr{Pull.SVal{}, True{}} <> stack, False{}, Parse.step(Lex.TOpenArr{}, Parse.P{False{}, root,
            qs})),
          True{},
        Equal.cong(Parse.P, Bool, xx => M6.prel(Pull.FArr{Pull.SVal{}, True{}} <> stack, False{}, xx), M6.pst(lx),
          Parse.step(Lex.TOpenArr{}, Parse.P{False{}, root, qs}), eq), oa_rel(stack, qs, root, hp, ev))))))

# an opening bracket
law p_oarr:
  for +tt: String
  for +tl: String
  for +lx: Lex.Lex
  for +stack: List<&2, Pull.Frame>
  for +qs: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +h_s: {D1.short(tl) == True{} : Bool}
  for +e: M6.lx_e(tt, tl, lx)
  for +hc: {M6.cm(lx, tl) == True{} : Bool}
  for +hp: {M6.prel(stack, False{}, Parse.P{False{}, root, qs}) == True{} : Bool}
  for +eq: {M6.pst(lx) == Parse.step(Lex.TOpenArr{}, Parse.P{False{}, root, qs}) : Parse.P}
  M4.sinv(tt, tl, Pull.punct.go(Lex.TOpenArr{}, stack, Pull.GNext{}, False{}))

def p_oarr(tt, tl, lx, stack, qs, root, h_s, e, hc, hp, eq):
  p_oarr.at(tt, tl, lx, stack, qs, root, h_s, e, hc, hp, eq, Pull.expect.val.go(stack), {==})

# an opening bracket where a value may go: the parser opens the same frame
law oo_rel:
  for +stack: List<&2, Pull.Frame>
  for +qs: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +hp: {M6.prel(stack, False{}, Parse.P{False{}, root, qs}) == True{} : Bool}
  for hv: {Pull.expect.val.go(stack) == True{} : Bool}
  {M6.prel(Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, Parse.step(Lex.TOpenObj{}, Parse.P{False{}, root,
    qs})) == True{} : Bool}

def oo_rel(stack, qs, root, hp, hv):
  match root:
    case None{}:
      rs = Equal.sym(Bool, Parse.step.ready(qs, None{}), True{}, ready_rel(stack, qs, None{}, hp, hv))
      %rs : {M6.prel(Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, Parse.step.open_obj.go(False{}, None{}, qs,
        _)) == True{} : Bool}
      hp
    case Some{+rv}:
      M6.no({M6.prel(Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, Parse.step(Lex.TOpenObj{}, Parse.P{False{},
          Some{rv},
        qs})) == True{} : Bool},
        M6.and_left(M6.rrel(False{}, Some{rv}, stack), M6.frels(stack, qs), hp))

# an opening bracket, once whether a value may go is named
law p_oobj.at:
  for +tt: String
  for +tl: String
  for +lx: Lex.Lex
  for +stack: List<&2, Pull.Frame>
  for +qs: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +h_s: {D1.short(tl) == True{} : Bool}
  for +e: M6.lx_e(tt, tl, lx)
  for +hc: {M6.cm(lx, tl) == True{} : Bool}
  for +hp: {M6.prel(stack, False{}, Parse.P{False{}, root, qs}) == True{} : Bool}
  for +eq: {M6.pst(lx) == Parse.step(Lex.TOpenObj{}, Parse.P{False{}, root, qs}) : Parse.P}
  for bv: Bool
  for +ev: {Pull.expect.val.go(stack) == bv : Bool}
  M4.sinv(tt, tl, Pull.punct.go(Lex.TOpenObj{}, stack, Pull.GNext{}, False{}))

def p_oobj.at(tt, tl, lx, stack, qs, root, h_s, e, hc, hp, eq, bv, ev):
  match bv:
    case False{}:
      es = Equal.sym(Bool, Pull.expect.val.go(stack), False{}, ev)
      %es : M4.sinv(tt, tl, Pull.punct.obj.if(stack, Pull.GNext{}, _))
      Unit{}
    case True{}:
      es = Equal.sym(Bool, Pull.expect.val.go(stack), True{}, ev)
      %es : M4.sinv(tt, tl, Pull.punct.obj.if(stack, Pull.GNext{}, _))
      (h_s, (lx, (e, (hc, Equal.trans(Bool, M6.prel(Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, M6.pst(lx)),
        M6.prel(Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, Parse.step(Lex.TOpenObj{}, Parse.P{False{}, root,
            qs})),
          True{},
        Equal.cong(Parse.P, Bool, xx => M6.prel(Pull.FObj{Pull.SKey{}, True{}} <> stack, False{}, xx), M6.pst(lx),
          Parse.step(Lex.TOpenObj{}, Parse.P{False{}, root, qs}), eq), oo_rel(stack, qs, root, hp, ev))))))

# an opening bracket
law p_oobj:
  for +tt: String
  for +tl: String
  for +lx: Lex.Lex
  for +stack: List<&2, Pull.Frame>
  for +qs: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +h_s: {D1.short(tl) == True{} : Bool}
  for +e: M6.lx_e(tt, tl, lx)
  for +hc: {M6.cm(lx, tl) == True{} : Bool}
  for +hp: {M6.prel(stack, False{}, Parse.P{False{}, root, qs}) == True{} : Bool}
  for +eq: {M6.pst(lx) == Parse.step(Lex.TOpenObj{}, Parse.P{False{}, root, qs}) : Parse.P}
  M4.sinv(tt, tl, Pull.punct.go(Lex.TOpenObj{}, stack, Pull.GNext{}, False{}))

def p_oobj(tt, tl, lx, stack, qs, root, h_s, e, hc, hp, eq):
  p_oobj.at(tt, tl, lx, stack, qs, root, h_s, e, hc, hp, eq, Pull.expect.val.go(stack), {==})

# a closing bracket after an element or of an empty array: the parser closes it too
law p_carr:
  for +tt: String
  for +tl: String
  for +lx: Lex.Lex
  for +stack: List<&2, Pull.Frame>
  for +qs: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +h_s: {D1.short(tl) == True{} : Bool}
  for +e: M6.lx_e(tt, tl, lx)
  for +hc: {M6.cm(lx, tl) == True{} : Bool}
  for +hp: {M6.prel(stack, False{}, Parse.P{False{}, root, qs}) == True{} : Bool}
  for +eq: {M6.pst(lx) == Parse.step(Lex.TCloseArr{}, Parse.P{False{}, root, qs}) : Parse.P}
  M4.sinv(tt, tl, Pull.close.arr(stack, Pull.GNext{}))

def p_carr(tt, tl, lx, stack, qs, root, h_s, e, hc, hp, eq):
  match stack:
    case Nil{}:
      Unit{}
    case Pull.FArr{Pull.SVal{}, True{}} <> +st:
      match qs:
        case Nil{}:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
              M6.and_right(M6.rrel(False{},
            root, Pull.FArr{Pull.SVal{}, True{}} <> st), M6.frels(Pull.FArr{Pull.SVal{}, True{}} <> st, []), hp))
        case Parse.FArr{V.JNull{}, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FArr{V.JNull{}, Parse.SValue{}}), M6.frels(st,
                qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{},
            True{}}, Parse.FArr{V.JNull{}, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{V.JBool{+i1}, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FArr{V.JBool{i1}, Parse.SValue{}}), M6.frels(st,
                qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{},
            True{}}, Parse.FArr{V.JBool{i1}, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{V.JNum{+i1}, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FArr{V.JNum{i1}, Parse.SValue{}}), M6.frels(st,
                qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{},
            True{}}, Parse.FArr{V.JNum{i1}, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{V.JStr{+i1}, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FArr{V.JStr{i1}, Parse.SValue{}}), M6.frels(st,
                qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{},
            True{}}, Parse.FArr{V.JStr{i1}, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{V.JArr{+i1}, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FArr{V.JArr{i1}, Parse.SValue{}}), M6.frels(st,
                qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{},
            True{}}, Parse.FArr{V.JArr{i1}, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{V.JObj{+i1}, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FArr{V.JObj{i1}, Parse.SValue{}}), M6.frels(st,
                qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{},
            True{}}, Parse.FArr{V.JObj{i1}, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{V.JNil{}, Parse.SValue{}} <> +qt:
          match root:
            case None{}:
              cl_inv_a(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JArr{V.JNil{}}, h_s, e, hc, hp, hv,
                  eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
                M6.and_left(M6.rrel(False{}, Some{rv}, Pull.FArr{Pull.SVal{}, True{}} <> st),
                    M6.frels(Pull.FArr{Pull.SVal{},
                True{}} <> st, Parse.FArr{V.JNil{}, Parse.SValue{}} <> qt), hp))
        case Parse.FArr{V.JCons{+i1, +i2}, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FArr{V.JCons{i1, i2}, Parse.SValue{}}),
                M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{},
            True{}}, Parse.FArr{V.JCons{i1, i2}, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{V.JPair{+i1, +i2, +i3}, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FArr{V.JPair{i1, i2, i3}, Parse.SValue{}}),
                M6.frels(st,
            qt), M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, True{}} <> st),
            Bool.and(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FArr{V.JPair{i1, i2, i3}, Parse.SValue{}}),
                M6.frels(st,
            qt)), hp)))
        case Parse.FArr{V.JSpan{+i1, +i2}, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FArr{V.JSpan{i1, i2}, Parse.SValue{}}),
                M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{},
            True{}}, Parse.FArr{V.JSpan{i1, i2}, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{V.JBind{+i1, +i2, +i3, +i4}, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FArr{V.JBind{i1, i2, i3, i4}, Parse.SValue{}}),
            M6.frels(st, qt), M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, True{}} <> st),
            Bool.and(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FArr{V.JBind{i1, i2, i3, i4}, Parse.SValue{}}),
            M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SComma{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{},
            True{}}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{},
            True{}}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SColon{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{},
            True{}}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st,
                qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{},
            True{}}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SComma{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st,
                qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{},
            True{}}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{},
            True{}}, Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SColon{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SVal{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SVal{}, True{}}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st,
                qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SVal{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SVal{},
            True{}}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt)), hp)))
    case Pull.FArr{Pull.SVal{}, False{}} <> +st:
      Unit{}
    case Pull.FArr{Pull.SCom{}, +ff} <> +st:
      match qs:
        case Nil{}:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
              M6.and_right(M6.rrel(False{},
            root, Pull.FArr{Pull.SCom{}, ff} <> st), M6.frels(Pull.FArr{Pull.SCom{}, ff} <> st, []), hp))
        case Parse.FArr{+items, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SCom{}, ff}, Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SCom{}, ff},
            Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{V.JNull{}, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_a(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JArr{V.reverse(V.JNull{}, V.JNil{})},
                h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FArr{Pull.SCom{}, ff} <> st), M6.frels(Pull.FArr{Pull.SCom{}, ff} <> st,
                Parse.FArr{V.JNull{}, Parse.SComma{}} <> qt), hp))
        case Parse.FArr{V.JBool{+i1}, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_a(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JArr{V.reverse(V.JBool{i1}, V.JNil{})},
                h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FArr{Pull.SCom{}, ff} <> st), M6.frels(Pull.FArr{Pull.SCom{}, ff} <> st,
                Parse.FArr{V.JBool{i1}, Parse.SComma{}} <> qt), hp))
        case Parse.FArr{V.JNum{+i1}, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_a(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JArr{V.reverse(V.JNum{i1}, V.JNil{})},
                h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FArr{Pull.SCom{}, ff} <> st), M6.frels(Pull.FArr{Pull.SCom{}, ff} <> st,
                Parse.FArr{V.JNum{i1}, Parse.SComma{}} <> qt), hp))
        case Parse.FArr{V.JStr{+i1}, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_a(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JArr{V.reverse(V.JStr{i1}, V.JNil{})},
                h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FArr{Pull.SCom{}, ff} <> st), M6.frels(Pull.FArr{Pull.SCom{}, ff} <> st,
                Parse.FArr{V.JStr{i1}, Parse.SComma{}} <> qt), hp))
        case Parse.FArr{V.JArr{+i1}, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_a(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JArr{V.reverse(V.JArr{i1}, V.JNil{})},
                h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FArr{Pull.SCom{}, ff} <> st), M6.frels(Pull.FArr{Pull.SCom{}, ff} <> st,
                Parse.FArr{V.JArr{i1}, Parse.SComma{}} <> qt), hp))
        case Parse.FArr{V.JObj{+i1}, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_a(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JArr{V.reverse(V.JObj{i1}, V.JNil{})},
                h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FArr{Pull.SCom{}, ff} <> st), M6.frels(Pull.FArr{Pull.SCom{}, ff} <> st,
                Parse.FArr{V.JObj{i1}, Parse.SComma{}} <> qt), hp))
        case Parse.FArr{V.JNil{}, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_a(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JArr{V.reverse(V.JNil{}, V.JNil{})},
                  h_s,
                e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FArr{Pull.SCom{}, ff} <> st), M6.frels(Pull.FArr{Pull.SCom{}, ff} <> st,
                Parse.FArr{V.JNil{}, Parse.SComma{}} <> qt), hp))
        case Parse.FArr{V.JCons{+i1, +i2}, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_a(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JArr{V.reverse(V.JCons{i1, i2},
                V.JNil{})}, h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FArr{Pull.SCom{}, ff} <> st), M6.frels(Pull.FArr{Pull.SCom{}, ff} <> st,
                Parse.FArr{V.JCons{i1, i2}, Parse.SComma{}} <> qt), hp))
        case Parse.FArr{V.JPair{+i1, +i2, +i3}, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_a(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JArr{V.reverse(V.JPair{i1, i2, i3},
                V.JNil{})}, h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FArr{Pull.SCom{}, ff} <> st), M6.frels(Pull.FArr{Pull.SCom{}, ff} <> st,
                Parse.FArr{V.JPair{i1, i2, i3}, Parse.SComma{}} <> qt), hp))
        case Parse.FArr{V.JSpan{+i1, +i2}, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_a(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JArr{V.reverse(V.JSpan{i1, i2},
                V.JNil{})}, h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FArr{Pull.SCom{}, ff} <> st), M6.frels(Pull.FArr{Pull.SCom{}, ff} <> st,
                Parse.FArr{V.JSpan{i1, i2}, Parse.SComma{}} <> qt), hp))
        case Parse.FArr{V.JBind{+i1, +i2, +i3, +i4}, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_a(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JArr{V.reverse(V.JBind{i1, i2, i3, i4},
                V.JNil{})}, h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FArr{Pull.SCom{}, ff} <> st), M6.frels(Pull.FArr{Pull.SCom{}, ff} <> st,
                Parse.FArr{V.JBind{i1, i2, i3, i4}, Parse.SComma{}} <> qt), hp))
        case Parse.FArr{+items, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SCom{}, ff}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SCom{}, ff},
            Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SColon{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SCom{}, ff}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SCom{}, ff},
            Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SCom{}, ff}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SCom{}, ff},
            Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SComma{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SCom{}, ff}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SCom{}, ff},
            Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SCom{}, ff}, Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SCom{}, ff},
            Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SColon{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.arr(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SCom{}, ff}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SCom{}, ff},
            Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt)), hp)))
    case Pull.FArr{Pull.SKey{}, +ff} <> +st:
      Unit{}
    case Pull.FArr{Pull.SCol{}, +ff} <> +st:
      Unit{}
    case Pull.FObj{Pull.SVal{}, +ff} <> +st:
      Unit{}
    case Pull.FObj{Pull.SCom{}, +ff} <> +st:
      Unit{}
    case Pull.FObj{Pull.SKey{}, True{}} <> +st:
      Unit{}
    case Pull.FObj{Pull.SKey{}, False{}} <> +st:
      Unit{}
    case Pull.FObj{Pull.SCol{}, +ff} <> +st:
      Unit{}

# a closing brace after a member or of an empty object: the parser closes it too
law p_cobj:
  for +tt: String
  for +tl: String
  for +lx: Lex.Lex
  for +stack: List<&2, Pull.Frame>
  for +qs: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +h_s: {D1.short(tl) == True{} : Bool}
  for +e: M6.lx_e(tt, tl, lx)
  for +hc: {M6.cm(lx, tl) == True{} : Bool}
  for +hp: {M6.prel(stack, False{}, Parse.P{False{}, root, qs}) == True{} : Bool}
  for +eq: {M6.pst(lx) == Parse.step(Lex.TCloseObj{}, Parse.P{False{}, root, qs}) : Parse.P}
  M4.sinv(tt, tl, Pull.close.obj(stack, Pull.GNext{}))

def p_cobj(tt, tl, lx, stack, qs, root, h_s, e, hc, hp, eq):
  match stack:
    case Nil{}:
      Unit{}
    case Pull.FArr{Pull.SVal{}, True{}} <> +st:
      Unit{}
    case Pull.FArr{Pull.SVal{}, False{}} <> +st:
      Unit{}
    case Pull.FArr{Pull.SCom{}, +ff} <> +st:
      Unit{}
    case Pull.FArr{Pull.SKey{}, +ff} <> +st:
      Unit{}
    case Pull.FArr{Pull.SCol{}, +ff} <> +st:
      Unit{}
    case Pull.FObj{Pull.SVal{}, +ff} <> +st:
      Unit{}
    case Pull.FObj{Pull.SCom{}, +ff} <> +st:
      match qs:
        case Nil{}:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
              M6.and_right(M6.rrel(False{},
            root, Pull.FObj{Pull.SCom{}, ff} <> st), M6.frels(Pull.FObj{Pull.SCom{}, ff} <> st, []), hp))
        case Parse.FArr{+items, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCom{}, ff}, Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCom{}, ff},
            Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SComma{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCom{}, ff}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCom{}, ff},
            Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCom{}, ff}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCom{}, ff},
            Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SColon{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCom{}, ff}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCom{}, ff},
            Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCom{}, ff}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCom{}, ff},
            Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{V.JNull{}, +kk, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_o(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JObj{V.reverse(V.JNull{}, V.JNil{})},
                h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FObj{Pull.SCom{}, ff} <> st), M6.frels(Pull.FObj{Pull.SCom{}, ff} <> st,
                Parse.FObj{V.JNull{}, kk, Parse.SComma{}} <> qt), hp))
        case Parse.FObj{V.JBool{+i1}, +kk, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_o(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JObj{V.reverse(V.JBool{i1}, V.JNil{})},
                h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FObj{Pull.SCom{}, ff} <> st), M6.frels(Pull.FObj{Pull.SCom{}, ff} <> st,
                Parse.FObj{V.JBool{i1}, kk, Parse.SComma{}} <> qt), hp))
        case Parse.FObj{V.JNum{+i1}, +kk, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_o(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JObj{V.reverse(V.JNum{i1}, V.JNil{})},
                h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FObj{Pull.SCom{}, ff} <> st), M6.frels(Pull.FObj{Pull.SCom{}, ff} <> st,
                Parse.FObj{V.JNum{i1}, kk, Parse.SComma{}} <> qt), hp))
        case Parse.FObj{V.JStr{+i1}, +kk, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_o(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JObj{V.reverse(V.JStr{i1}, V.JNil{})},
                h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FObj{Pull.SCom{}, ff} <> st), M6.frels(Pull.FObj{Pull.SCom{}, ff} <> st,
                Parse.FObj{V.JStr{i1}, kk, Parse.SComma{}} <> qt), hp))
        case Parse.FObj{V.JArr{+i1}, +kk, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_o(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JObj{V.reverse(V.JArr{i1}, V.JNil{})},
                h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FObj{Pull.SCom{}, ff} <> st), M6.frels(Pull.FObj{Pull.SCom{}, ff} <> st,
                Parse.FObj{V.JArr{i1}, kk, Parse.SComma{}} <> qt), hp))
        case Parse.FObj{V.JObj{+i1}, +kk, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_o(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JObj{V.reverse(V.JObj{i1}, V.JNil{})},
                h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FObj{Pull.SCom{}, ff} <> st), M6.frels(Pull.FObj{Pull.SCom{}, ff} <> st,
                Parse.FObj{V.JObj{i1}, kk, Parse.SComma{}} <> qt), hp))
        case Parse.FObj{V.JNil{}, +kk, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_o(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JObj{V.reverse(V.JNil{}, V.JNil{})},
                  h_s,
                e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FObj{Pull.SCom{}, ff} <> st), M6.frels(Pull.FObj{Pull.SCom{}, ff} <> st,
                Parse.FObj{V.JNil{}, kk, Parse.SComma{}} <> qt), hp))
        case Parse.FObj{V.JCons{+i1, +i2}, +kk, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_o(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JObj{V.reverse(V.JCons{i1, i2},
                V.JNil{})}, h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FObj{Pull.SCom{}, ff} <> st), M6.frels(Pull.FObj{Pull.SCom{}, ff} <> st,
                Parse.FObj{V.JCons{i1, i2}, kk, Parse.SComma{}} <> qt), hp))
        case Parse.FObj{V.JPair{+i1, +i2, +i3}, +kk, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_o(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JObj{V.reverse(V.JPair{i1, i2, i3},
                V.JNil{})}, h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FObj{Pull.SCom{}, ff} <> st), M6.frels(Pull.FObj{Pull.SCom{}, ff} <> st,
                Parse.FObj{V.JPair{i1, i2, i3}, kk, Parse.SComma{}} <> qt), hp))
        case Parse.FObj{V.JSpan{+i1, +i2}, +kk, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_o(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JObj{V.reverse(V.JSpan{i1, i2},
                V.JNil{})}, h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FObj{Pull.SCom{}, ff} <> st), M6.frels(Pull.FObj{Pull.SCom{}, ff} <> st,
                Parse.FObj{V.JSpan{i1, i2}, kk, Parse.SComma{}} <> qt), hp))
        case Parse.FObj{V.JBind{+i1, +i2, +i3, +i4}, +kk, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              cl_inv_o(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JObj{V.reverse(V.JBind{i1, i2, i3, i4},
                V.JNil{})}, h_s, e, hc, hp, hv, eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FObj{Pull.SCom{}, ff} <> st), M6.frels(Pull.FObj{Pull.SCom{}, ff} <> st,
                Parse.FObj{V.JBind{i1, i2, i3, i4}, kk, Parse.SComma{}} <> qt), hp))
        case Parse.FObj{+items, +kk, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCom{}, ff}, Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCom{}, ff},
            Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SColon{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCom{}, ff}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCom{}, ff},
            Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt)), hp)))
    case Pull.FObj{Pull.SKey{}, True{}} <> +st:
      match qs:
        case Nil{}:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
              M6.and_right(M6.rrel(False{},
            root, Pull.FObj{Pull.SKey{}, True{}} <> st), M6.frels(Pull.FObj{Pull.SKey{}, True{}} <> st, []), hp))
        case Parse.FArr{+items, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
            True{}}, Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SComma{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
            True{}}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
            True{}}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SColon{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
            True{}}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st,
                qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
            True{}}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SComma{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st,
                qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
            True{}}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{V.JNull{}, +kk, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FObj{V.JNull{}, kk, Parse.SKey{}}), M6.frels(st,
                qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
            True{}}, Parse.FObj{V.JNull{}, kk, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{V.JBool{+i1}, +kk, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FObj{V.JBool{i1}, kk, Parse.SKey{}}),
                M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
            True{}}, Parse.FObj{V.JBool{i1}, kk, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{V.JNum{+i1}, +kk, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FObj{V.JNum{i1}, kk, Parse.SKey{}}), M6.frels(st,
                qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
            True{}}, Parse.FObj{V.JNum{i1}, kk, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{V.JStr{+i1}, +kk, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FObj{V.JStr{i1}, kk, Parse.SKey{}}), M6.frels(st,
                qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
            True{}}, Parse.FObj{V.JStr{i1}, kk, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{V.JArr{+i1}, +kk, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FObj{V.JArr{i1}, kk, Parse.SKey{}}), M6.frels(st,
                qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
            True{}}, Parse.FObj{V.JArr{i1}, kk, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{V.JObj{+i1}, +kk, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FObj{V.JObj{i1}, kk, Parse.SKey{}}), M6.frels(st,
                qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
            True{}}, Parse.FObj{V.JObj{i1}, kk, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{V.JNil{}, +kk, Parse.SKey{}} <> +qt:
          match root:
            case None{}:
              cl_inv_o(tt, tl, st, hv => M4.land_c(tt, tl, lx, st, qt, None{}, V.JObj{V.JNil{}}, h_s, e, hc, hp, hv,
                  eq))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
                M6.and_left(M6.rrel(False{}, Some{rv}, Pull.FObj{Pull.SKey{}, True{}} <> st),
                    M6.frels(Pull.FObj{Pull.SKey{},
                True{}} <> st, Parse.FObj{V.JNil{}, kk, Parse.SKey{}} <> qt), hp))
        case Parse.FObj{V.JCons{+i1, +i2}, +kk, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FObj{V.JCons{i1, i2}, kk, Parse.SKey{}}),
                M6.frels(st,
            qt), M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, True{}} <> st),
            Bool.and(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FObj{V.JCons{i1, i2}, kk, Parse.SKey{}}),
                M6.frels(st,
            qt)), hp)))
        case Parse.FObj{V.JPair{+i1, +i2, +i3}, +kk, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FObj{V.JPair{i1, i2, i3}, kk, Parse.SKey{}}),
                M6.frels(st,
            qt), M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, True{}} <> st),
            Bool.and(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FObj{V.JPair{i1, i2, i3}, kk, Parse.SKey{}}),
                M6.frels(st,
            qt)), hp)))
        case Parse.FObj{V.JSpan{+i1, +i2}, +kk, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FObj{V.JSpan{i1, i2}, kk, Parse.SKey{}}),
                M6.frels(st,
            qt), M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, True{}} <> st),
            Bool.and(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FObj{V.JSpan{i1, i2}, kk, Parse.SKey{}}),
                M6.frels(st,
            qt)), hp)))
        case Parse.FObj{V.JBind{+i1, +i2, +i3, +i4}, +kk, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FObj{V.JBind{i1, i2, i3, i4}, kk, Parse.SKey{}}),
            M6.frels(st, qt), M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, True{}} <> st),
            Bool.and(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FObj{V.JBind{i1, i2, i3, i4}, kk, Parse.SKey{}}),
            M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SColon{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.close.obj(Pull.FObj{Pull.SKey{}, True{}} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, True{}}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st,
                qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, True{}} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
            True{}}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt)), hp)))
    case Pull.FObj{Pull.SKey{}, False{}} <> +st:
      Unit{}
    case Pull.FObj{Pull.SCol{}, +ff} <> +st:
      Unit{}

# a colon after a member's name: the parser waits for the value too
law p_colon:
  for +tt: String
  for +tl: String
  for +lx: Lex.Lex
  for +stack: List<&2, Pull.Frame>
  for +qs: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +h_s: {D1.short(tl) == True{} : Bool}
  for +e: M6.lx_e(tt, tl, lx)
  for +hc: {M6.cm(lx, tl) == True{} : Bool}
  for +hp: {M6.prel(stack, False{}, Parse.P{False{}, root, qs}) == True{} : Bool}
  for +eq: {M6.pst(lx) == Parse.step(Lex.TColon{}, Parse.P{False{}, root, qs}) : Parse.P}
  M4.sinv(tt, tl, Pull.punct.colon(stack, Pull.GNext{}))

def p_colon(tt, tl, lx, stack, qs, root, h_s, e, hc, hp, eq):
  match stack:
    case Nil{}:
      Unit{}
    case Pull.FArr{Pull.SVal{}, True{}} <> +st:
      Unit{}
    case Pull.FArr{Pull.SVal{}, False{}} <> +st:
      Unit{}
    case Pull.FArr{Pull.SCom{}, +ff} <> +st:
      Unit{}
    case Pull.FArr{Pull.SKey{}, +ff} <> +st:
      Unit{}
    case Pull.FArr{Pull.SCol{}, +ff} <> +st:
      Unit{}
    case Pull.FObj{Pull.SVal{}, +ff} <> +st:
      Unit{}
    case Pull.FObj{Pull.SCom{}, +ff} <> +st:
      Unit{}
    case Pull.FObj{Pull.SKey{}, True{}} <> +st:
      Unit{}
    case Pull.FObj{Pull.SKey{}, False{}} <> +st:
      Unit{}
    case Pull.FObj{Pull.SCol{}, +ff} <> +st:
      match qs:
        case Nil{}:
          M6.no(M4.sinv(tt, tl, Pull.punct.colon(Pull.FObj{Pull.SCol{}, ff} <> st, Pull.GNext{})),
              M6.and_right(M6.rrel(False{},
            root, Pull.FObj{Pull.SCol{}, ff} <> st), M6.frels(Pull.FObj{Pull.SCol{}, ff} <> st, []), hp))
        case Parse.FArr{+items, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.colon(Pull.FObj{Pull.SCol{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCol{}, ff}, Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCol{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCol{}, ff},
            Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SComma{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.colon(Pull.FObj{Pull.SCol{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCol{}, ff}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCol{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCol{}, ff},
            Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.colon(Pull.FObj{Pull.SCol{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCol{}, ff}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCol{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCol{}, ff},
            Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SColon{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.colon(Pull.FObj{Pull.SCol{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCol{}, ff}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCol{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCol{}, ff},
            Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.colon(Pull.FObj{Pull.SCol{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCol{}, ff}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCol{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCol{}, ff},
            Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SComma{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.colon(Pull.FObj{Pull.SCol{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCol{}, ff}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCol{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCol{}, ff},
            Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.colon(Pull.FObj{Pull.SCol{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCol{}, ff}, Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCol{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCol{}, ff},
            Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SColon{}} <> +qt:
          match root:
            case None{}:
              (h_s, (lx, (e, (hc, Equal.trans(Bool, M6.prel(Pull.FObj{Pull.SVal{}, False{}} <> st, False{}, M6.pst(lx)),
                M6.prel(Pull.FObj{Pull.SVal{}, False{}} <> st, False{},
                Parse.P{False{}, None{}, Parse.FObj{items, kk, Parse.SValue{}} <> qt}), True{}, Equal.cong(Parse.P,
                  Bool, xx => M6.prel(Pull.FObj{Pull.SVal{}, False{}} <> st, False{}, xx), M6.pst(lx),
                Parse.P{False{}, None{}, Parse.FObj{items, kk, Parse.SValue{}} <> qt}, eq), hp)))))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.punct.colon(Pull.FObj{Pull.SCol{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FObj{Pull.SCol{}, ff} <> st), M6.frels(Pull.FObj{Pull.SCol{}, ff} <> st,
                    Parse.FObj{items,
                kk, Parse.SColon{}} <> qt), hp))

# a comma after a value: the parser waits for the next element or member too
law p_comma:
  for +tt: String
  for +tl: String
  for +lx: Lex.Lex
  for +stack: List<&2, Pull.Frame>
  for +qs: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +h_s: {D1.short(tl) == True{} : Bool}
  for +e: M6.lx_e(tt, tl, lx)
  for +hc: {M6.cm(lx, tl) == True{} : Bool}
  for +hp: {M6.prel(stack, False{}, Parse.P{False{}, root, qs}) == True{} : Bool}
  for +eq: {M6.pst(lx) == Parse.step(Lex.TComma{}, Parse.P{False{}, root, qs}) : Parse.P}
  M4.sinv(tt, tl, Pull.punct.comma(stack, Pull.GNext{}))

def p_comma(tt, tl, lx, stack, qs, root, h_s, e, hc, hp, eq):
  match stack:
    case Nil{}:
      Unit{}
    case Pull.FArr{Pull.SVal{}, True{}} <> +st:
      Unit{}
    case Pull.FArr{Pull.SVal{}, False{}} <> +st:
      Unit{}
    case Pull.FArr{Pull.SCom{}, +ff} <> +st:
      match qs:
        case Nil{}:
          M6.no(M4.sinv(tt, tl, Pull.punct.comma(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
              M6.and_right(M6.rrel(False{},
            root, Pull.FArr{Pull.SCom{}, ff} <> st), M6.frels(Pull.FArr{Pull.SCom{}, ff} <> st, []), hp))
        case Parse.FArr{+items, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.comma(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SCom{}, ff}, Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SCom{}, ff},
            Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              (h_s, (lx, (e, (hc, Equal.trans(Bool, M6.prel(Pull.FArr{Pull.SVal{}, False{}} <> st, False{}, M6.pst(lx)),
                M6.prel(Pull.FArr{Pull.SVal{}, False{}} <> st, False{},
                Parse.P{False{}, None{}, Parse.FArr{items, Parse.SValue{}} <> qt}), True{}, Equal.cong(Parse.P, Bool,
                  xx => M6.prel(Pull.FArr{Pull.SVal{}, False{}} <> st, False{}, xx), M6.pst(lx),
                Parse.P{False{}, None{}, Parse.FArr{items, Parse.SValue{}} <> qt}, eq), hp)))))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.punct.comma(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FArr{Pull.SCom{}, ff} <> st), M6.frels(Pull.FArr{Pull.SCom{}, ff} <> st,
                    Parse.FArr{items,
                Parse.SComma{}} <> qt), hp))
        case Parse.FArr{+items, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.comma(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SCom{}, ff}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SCom{}, ff},
            Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SColon{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.comma(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SCom{}, ff}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SCom{}, ff},
            Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.comma(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SCom{}, ff}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SCom{}, ff},
            Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SComma{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.comma(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SCom{}, ff}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SCom{}, ff},
            Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.comma(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SCom{}, ff}, Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SCom{}, ff},
            Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SColon{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.comma(Pull.FArr{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FArr{Pull.SCom{}, ff}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FArr{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FArr{Pull.SCom{}, ff},
            Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt)), hp)))
    case Pull.FArr{Pull.SKey{}, +ff} <> +st:
      Unit{}
    case Pull.FArr{Pull.SCol{}, +ff} <> +st:
      Unit{}
    case Pull.FObj{Pull.SVal{}, +ff} <> +st:
      Unit{}
    case Pull.FObj{Pull.SCom{}, +ff} <> +st:
      match qs:
        case Nil{}:
          M6.no(M4.sinv(tt, tl, Pull.punct.comma(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
              M6.and_right(M6.rrel(False{},
            root, Pull.FObj{Pull.SCom{}, ff} <> st), M6.frels(Pull.FObj{Pull.SCom{}, ff} <> st, []), hp))
        case Parse.FArr{+items, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.comma(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCom{}, ff}, Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCom{}, ff},
            Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SComma{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.comma(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCom{}, ff}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCom{}, ff},
            Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.comma(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCom{}, ff}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCom{}, ff},
            Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FArr{+items, Parse.SColon{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.comma(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCom{}, ff}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCom{}, ff},
            Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SValue{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.comma(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCom{}, ff}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCom{}, ff},
            Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SComma{}} <> +qt:
          match root:
            case None{}:
              (h_s, (lx, (e, (hc, Equal.trans(Bool, M6.prel(Pull.FObj{Pull.SKey{}, False{}} <> st, False{}, M6.pst(lx)),
                M6.prel(Pull.FObj{Pull.SKey{}, False{}} <> st, False{},
                Parse.P{False{}, None{}, Parse.FObj{items, Parse.KOwn{""}, Parse.SKey{}} <> qt}), True{},
                  Equal.cong(Parse.P, Bool, xx => M6.prel(Pull.FObj{Pull.SKey{}, False{}} <> st, False{}, xx),
                      M6.pst(lx),
                Parse.P{False{}, None{}, Parse.FObj{items, Parse.KOwn{""}, Parse.SKey{}} <> qt}, eq), hp)))))
            case Some{+rv}:
              M6.no(M4.sinv(tt, tl, Pull.punct.comma(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
                  M6.and_left(M6.rrel(False{},
                Some{rv}, Pull.FObj{Pull.SCom{}, ff} <> st), M6.frels(Pull.FObj{Pull.SCom{}, ff} <> st,
                    Parse.FObj{items,
                kk, Parse.SComma{}} <> qt), hp))
        case Parse.FObj{+items, +kk, Parse.SKey{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.comma(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCom{}, ff}, Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCom{}, ff},
            Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st, qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SColon{}} <> +qt:
          M6.no(M4.sinv(tt, tl, Pull.punct.comma(Pull.FObj{Pull.SCom{}, ff} <> st, Pull.GNext{})),
            M6.and_left(M6.frel(Pull.FObj{Pull.SCom{}, ff}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt),
            M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SCom{}, ff} <> st),
                Bool.and(M6.frel(Pull.FObj{Pull.SCom{}, ff},
            Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt)), hp)))
    case Pull.FObj{Pull.SKey{}, True{}} <> +st:
      Unit{}
    case Pull.FObj{Pull.SKey{}, False{}} <> +st:
      Unit{}
    case Pull.FObj{Pull.SCol{}, +ff} <> +st:
      Unit{}

# a punctuation token between tokens: the cursor fails, or it and the parser
# on the same token stay in step
law punct_inv:
  for +tok: Lex.Tok
  for +tt: String
  for +tl: String
  for +lx: Lex.Lex
  for +stack: List<&2, Pull.Frame>
  for +qs: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +h_s: {D1.short(tl) == True{} : Bool}
  for +e: M6.lx_e(tt, tl, lx)
  for +hc: {M6.cm(lx, tl) == True{} : Bool}
  for +hp: {M6.prel(stack, False{}, Parse.P{False{}, root, qs}) == True{} : Bool}
  for +eq: {M6.pst(lx) == Parse.step(M6.den(tok), Parse.P{False{}, root, qs}) : Parse.P}
  M4.sinv(tt, tl, Pull.punct.go(tok, stack, Pull.GNext{}, False{}))

def punct_inv(tok, tt, tl, lx, stack, qs, root, h_s, e, hc, hp, eq):
  match tok:
    case Lex.TOpenArr{}:
      p_oarr(tt, tl, lx, stack, qs, root, h_s, e, hc, hp, eq)
    case Lex.TCloseArr{}:
      p_carr(tt, tl, lx, stack, qs, root, h_s, e, hc, hp, eq)
    case Lex.TOpenObj{}:
      p_oobj(tt, tl, lx, stack, qs, root, h_s, e, hc, hp, eq)
    case Lex.TCloseObj{}:
      p_cobj(tt, tl, lx, stack, qs, root, h_s, e, hc, hp, eq)
    case Lex.TColon{}:
      p_colon(tt, tl, lx, stack, qs, root, h_s, e, hc, hp, eq)
    case Lex.TComma{}:
      p_comma(tt, tl, lx, stack, qs, root, h_s, e, hc, hp, eq)
    case Lex.TStr{_}:
      Unit{}
    case Lex.TWord{_}:
      Unit{}
    case Lex.TStrS{_, _}:
      Unit{}
    case Lex.TWordS{_, _}:
      Unit{}
    case Lex.TBad{}:
      Unit{}

# a class that ends a word and starts no other: whitespace, punctuation, a quote
def kok(cls: Lex.Class) -> Bool:
  match cls:
    case Lex.CPunct{_}:
      True{}
    case Lex.CQuote{}:
      True{}
    case Lex.CSpace{}:
      True{}
    case _:
      False{}

# a character that ends a word, fed to a lexer between tokens, acts as if the
# word had already been pushed
law feed_cls:
  for +ch: Char
  for +lx: Lex.Lex
  for +xx: String
  for cls: Lex.Class
  for +ecls: {Lex.classify(ch) == cls : Lex.Class}
  for hc: {M6.cm(lx, SCon{ch, xx}) == True{} : Bool}
  for hk: {kok(cls) == True{} : Bool}
  {Lex.feed(ch, lx) == Lex.step(Lex.Idle{}, cls, ch, [], M6.eff(lx)) : Lex.Lex}

def feed_cls(ch, lx, _xx, cls, ecls, hc, hk):
  match lx:
    case Lex.Lex{Lex.Idle{}, +bf, +tk}:
      match cls:
        case Lex.CPunct{+tt}:
          es = Equal.sym(Lex.Class, Lex.classify(ch), Lex.CPunct{tt}, ecls)
          %es : {Lex.step(Lex.Idle{}, _, ch, bf, tk) == Lex.step(Lex.Idle{}, Lex.CPunct{tt}, ch, [],
            M6.eff(Lex.Lex{Lex.Idle{}, bf, tk})) : Lex.Lex}
          {==}
        case Lex.CQuote{}:
          es = Equal.sym(Lex.Class, Lex.classify(ch), Lex.CQuote{}, ecls)
          %es : {Lex.step(Lex.Idle{}, _, ch, bf, tk) == Lex.step(Lex.Idle{}, Lex.CQuote{}, ch, [],
            M6.eff(Lex.Lex{Lex.Idle{}, bf, tk})) : Lex.Lex}
          {==}
        case Lex.CSpace{}:
          es = Equal.sym(Lex.Class, Lex.classify(ch), Lex.CSpace{}, ecls)
          %es : {Lex.step(Lex.Idle{}, _, ch, bf, tk) == Lex.step(Lex.Idle{}, Lex.CSpace{}, ch, [],
            M6.eff(Lex.Lex{Lex.Idle{}, bf, tk})) : Lex.Lex}
          {==}
        case Lex.CBack{}:
          M6.no({Lex.feed(ch, Lex.Lex{Lex.Idle{}, bf, tk}) == Lex.step(Lex.Idle{}, Lex.CBack{}, ch, [],
            M6.eff(Lex.Lex{Lex.Idle{}, bf, tk})) : Lex.Lex}, hk)
        case Lex.COther{}:
          M6.no({Lex.feed(ch, Lex.Lex{Lex.Idle{}, bf, tk}) == Lex.step(Lex.Idle{}, Lex.COther{}, ch, [],
            M6.eff(Lex.Lex{Lex.Idle{}, bf, tk})) : Lex.Lex}, hk)
    case Lex.Lex{Lex.Word{}, +bf, +tk}:
      match cls:
        case Lex.CPunct{+tt}:
          es = Equal.sym(Lex.Class, Lex.classify(ch), Lex.CPunct{tt}, ecls)
          %es : {Lex.step(Lex.Word{}, _, ch, bf, tk) == Lex.step(Lex.Idle{}, Lex.CPunct{tt}, ch, [],
            M6.eff(Lex.Lex{Lex.Word{}, bf, tk})) : Lex.Lex}
          {==}
        case Lex.CQuote{}:
          es = Equal.sym(Lex.Class, Lex.classify(ch), Lex.CQuote{}, ecls)
          %es : {Lex.step(Lex.Word{}, _, ch, bf, tk) == Lex.step(Lex.Idle{}, Lex.CQuote{}, ch, [],
            M6.eff(Lex.Lex{Lex.Word{}, bf, tk})) : Lex.Lex}
          {==}
        case Lex.CSpace{}:
          es = Equal.sym(Lex.Class, Lex.classify(ch), Lex.CSpace{}, ecls)
          %es : {Lex.step(Lex.Word{}, _, ch, bf, tk) == Lex.step(Lex.Idle{}, Lex.CSpace{}, ch, [],
            M6.eff(Lex.Lex{Lex.Word{}, bf, tk})) : Lex.Lex}
          {==}
        case Lex.CBack{}:
          M6.no({Lex.feed(ch, Lex.Lex{Lex.Word{}, bf, tk}) == Lex.step(Lex.Idle{}, Lex.CBack{}, ch, [],
            M6.eff(Lex.Lex{Lex.Word{}, bf, tk})) : Lex.Lex}, hk)
        case Lex.COther{}:
          M6.no({Lex.feed(ch, Lex.Lex{Lex.Word{}, bf, tk}) == Lex.step(Lex.Idle{}, Lex.COther{}, ch, [],
            M6.eff(Lex.Lex{Lex.Word{}, bf, tk})) : Lex.Lex}, hk)
    case Lex.Lex{Lex.Str{}, +bf, +tk}:
      M6.no({Lex.feed(ch, Lex.Lex{Lex.Str{}, bf, tk}) == Lex.step(Lex.Idle{}, cls, ch, [], M6.eff(Lex.Lex{Lex.Str{}, bf,
        tk})) : Lex.Lex}, hc)
    case Lex.Lex{Lex.Esc{}, +bf, +tk}:
      M6.no({Lex.feed(ch, Lex.Lex{Lex.Esc{}, bf, tk}) == Lex.step(Lex.Idle{}, cls, ch, [], M6.eff(Lex.Lex{Lex.Esc{}, bf,
        tk})) : Lex.Lex}, hc)
    case Lex.Lex{Lex.Uni{+m1, +m2}, +bf, +tk}:
      M6.no({Lex.feed(ch, Lex.Lex{Lex.Uni{m1, m2}, bf, tk}) == Lex.step(Lex.Idle{}, cls, ch, [],
          M6.eff(Lex.Lex{Lex.Uni{m1,
        m2}, bf, tk})) : Lex.Lex}, hc)
    case Lex.Lex{Lex.Hi{+m1}, +bf, +tk}:
      M6.no({Lex.feed(ch, Lex.Lex{Lex.Hi{m1}, bf, tk}) == Lex.step(Lex.Idle{}, cls, ch, [], M6.eff(Lex.Lex{Lex.Hi{m1},
          bf,
        tk})) : Lex.Lex}, hc)
    case Lex.Lex{Lex.HiEsc{+m1}, +bf, +tk}:
      M6.no({Lex.feed(ch, Lex.Lex{Lex.HiEsc{m1}, bf, tk}) == Lex.step(Lex.Idle{}, cls, ch, [],
          M6.eff(Lex.Lex{Lex.HiEsc{m1},
        bf, tk})) : Lex.Lex}, hc)
    case Lex.Lex{Lex.Lo{+m1, +m2, +m3}, +bf, +tk}:
      M6.no({Lex.feed(ch, Lex.Lex{Lex.Lo{m1, m2, m3}, bf, tk}) == Lex.step(Lex.Idle{}, cls, ch, [],
          M6.eff(Lex.Lex{Lex.Lo{m1,
        m2, m3}, bf, tk})) : Lex.Lex}, hc)
    case Lex.Lex{Lex.Bad{}, +bf, +tk}:
      M6.no({Lex.feed(ch, Lex.Lex{Lex.Bad{}, bf, tk}) == Lex.step(Lex.Idle{}, cls, ch, [], M6.eff(Lex.Lex{Lex.Bad{}, bf,
        tk})) : Lex.Lex}, hc)

# a punctuation character, once the parser's state is named
law idle_pu.at:
  for +tok: Lex.Tok
  for +tt: String
  for +ch: Char
  for +tl: String
  for +stack: List<&2, Pull.Frame>
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for +lx: Lex.Lex
  for +e: M6.lx_e(tt, SCon{ch, tl}, lx)
  for +hc: {M6.cm(lx, SCon{ch, tl}) == True{} : Bool}
  for +hp: {M6.prel(stack, False{}, M6.pst(lx)) == True{} : Bool}
  for +pp: Parse.P
  for +epp: {M6.pst(lx) == pp : Parse.P}
  for +ecls: {Lex.classify(ch) == Lex.CPunct{tok} : Lex.Class}
  M4.sinv(tt, tl, Pull.punct.go(tok, stack, Pull.GNext{}, False{}))

def idle_pu.at(tok, tt, ch, tl, stack, h_s, lx, e, hc, hp, pp, epp, ecls):
  match pp:
    case Parse.P{True{}, +r1, +q1}:
      M6.no(M4.sinv(tt, tl, Pull.punct.go(tok, stack, Pull.GNext{}, False{})), Equal.trans(Bool, False{},
        M6.prel(stack, False{}, M6.pst(lx)), True{}, Equal.cong(Parse.P, Bool, xx => M6.prel(stack, False{}, xx),
          Parse.P{True{}, r1, q1},
        M6.pst(lx), Equal.sym(Parse.P, M6.pst(lx), Parse.P{True{}, r1, q1}, epp)), hp))
    case Parse.P{False{}, +root, +qs}:
      +lx2 = M4.lxi(tok <> M6.eff(lx))
      punct_inv(tok, tt, tl, lx2, stack, qs, root, M2.short_tail(ch, tl, h_s),
        Equal.trans(Lex.Lex, Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.feed(ch, lx)),
          Lex.run(String.to_list(tl), lx2), e, Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list(tl), xx),
          Lex.feed(ch, lx), lx2, feed_cls(ch, lx, tl, Lex.CPunct{tok}, ecls, hc, {==}))), {==},
        Equal.trans(Bool, M6.prel(stack, False{}, Parse.P{False{}, root, qs}), M6.prel(stack, False{}, M6.pst(lx)),
            True{},
          Equal.cong(Parse.P, Bool, xx => M6.prel(stack, False{}, xx), Parse.P{False{}, root, qs}, M6.pst(lx),
            Equal.sym(Parse.P, M6.pst(lx), Parse.P{False{}, root, qs}, epp)), hp),
        Equal.trans(Parse.P, M6.pst(lx2), Parse.step(M6.den(tok), M6.pst(lx)), Parse.step(M6.den(tok), Parse.P{False{},
            root, qs}),
          M4.pst_push(tok, M6.eff(lx)), Equal.cong(Parse.P, Parse.P, xx => Parse.step(M6.den(tok), xx), M6.pst(lx),
            Parse.P{False{}, root, qs}, epp)))

# one character between tokens, by its class: the cursor fails or stays in step
law idle_qu.at:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +stack: List<&2, Pull.Frame>
    for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for +lx: Lex.Lex
  for +e: M6.lx_e(tt, SCon{ch, tl}, lx)
  for +hc: {M6.cm(lx, SCon{ch, tl}) == True{} : Bool}
  for +hp: {M6.prel(stack, False{}, M6.pst(lx)) == True{} : Bool}
  for +ecls: {Lex.classify(ch) == Lex.CQuote{} : Lex.Class}
  for bb: Bool
  for +eb: {Pull.expect.str.go(stack) == bb : Bool}
  M4.sinv(tt, tl, Pull.look.quote(stack, Pull.GNext{}, False{}, Pull.expect.str.go(stack)))

def idle_qu.at(tt, ch, tl, stack, h_s, lx, e, hc, hp, ecls, bb, eb):
  match bb:
    case False{}:
      es = Equal.sym(Bool, Pull.expect.str.go(stack), False{}, eb)
      %es : M4.sinv(tt, tl, Pull.look.quote(stack, Pull.GNext{}, False{}, _))
      Unit{}
    case True{}:
      es = Equal.sym(Bool, Pull.expect.str.go(stack), True{}, eb)
      %es : M4.sinv(tt, tl, Pull.look.quote(stack, Pull.GNext{}, False{}, _))
      (M2.short_tail(ch, tl, h_s), ({==}, (Lex.Lex{Lex.Str{}, [], M6.eff(lx)}, (Equal.trans(Lex.Lex,
        Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.feed(ch, lx)),
            Lex.run(String.to_list(tl),
        Lex.Lex{Lex.Str{}, [], M6.eff(lx)}), e, Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list(tl), xx),
        Lex.feed(ch, lx), Lex.Lex{Lex.Str{}, [], M6.eff(lx)}, feed_cls(ch, lx, tl, Lex.CQuote{}, ecls, hc, {==}))),
            ({==},
        hp)))))

law idle_ot.go:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +stack: List<&2, Pull.Frame>
    for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for +lx: Lex.Lex
  for +e: M6.lx_e(tt, SCon{ch, tl}, lx)
  for +hc: {M6.cm(lx, SCon{ch, tl}) == True{} : Bool}
  for +hp: {M6.prel(stack, False{}, M6.pst(lx)) == True{} : Bool}
  for +ecls: {Lex.classify(ch) == Lex.COther{} : Lex.Class}
  for +eb: {Pull.expect.val.go(stack) == True{} : Bool}
  M4.sinv(tt, tl, Pull.S{Pull.MWord{[ch], 1, V.num.ok.step(V.NStart{}, Char.to_u32(ch))}, stack, Pull.GNext{}, False{},
    False{}})

def idle_ot.go(tt, ch, tl, stack, h_s, lx, e, hc, hp, ecls, eb):
  match lx:
    case Lex.Lex{Lex.Idle{}, +bf, +tk}:
      +lx2 = M4.lxw([ch], tk)
      ({==}, (eb, (M2.short_tail(ch, tl, h_s), ({==}, (SCon{ch, tl}, (M2.sdrop_zero(tl, tl, {==}), (M2.rev_zero(tl, 0,
          [ch]),
        (h_s, (tk, (Equal.trans(Lex.Lex, Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl),
          Lex.feed(ch, Lex.Lex{Lex.Idle{}, bf, tk})), Lex.run(String.to_list(tl), lx2), e,
          Equal.cong(Lex.Class, Lex.Lex, xx => Lex.run(String.to_list(tl), Lex.step(Lex.Idle{}, xx, ch, bf, tk)),
            Lex.classify(ch), Lex.COther{}, ecls)), hp))))))))))
    case Lex.Lex{Lex.Word{}, +bf, +tk}:
      M6.no(M4.sinv(tt, tl, Pull.S{Pull.MWord{[ch], 1, V.num.ok.step(V.NStart{}, Char.to_u32(ch))}, stack, Pull.GNext{},
        False{}, False{}}), Equal.trans(Bool, False{}, Bool.not(M6.is_other(Lex.classify(ch))), True{},
        Equal.sym(Bool, Bool.not(M6.is_other(Lex.classify(ch))), False{}, Equal.cong(Lex.Class, Bool,
          xx => Bool.not(M6.is_other(xx)), Lex.classify(ch), Lex.COther{}, ecls)), hc))
    case Lex.Lex{Lex.Str{}, +bf, +tk}:
      M6.no(M4.sinv(tt, tl, Pull.S{Pull.MWord{[ch], 1, V.num.ok.step(V.NStart{}, Char.to_u32(ch))}, stack, Pull.GNext{},
        False{}, False{}}), hc)
    case Lex.Lex{Lex.Esc{}, +bf, +tk}:
      M6.no(M4.sinv(tt, tl, Pull.S{Pull.MWord{[ch], 1, V.num.ok.step(V.NStart{}, Char.to_u32(ch))}, stack, Pull.GNext{},
        False{}, False{}}), hc)
    case Lex.Lex{Lex.Uni{+m1, +m2}, +bf, +tk}:
      M6.no(M4.sinv(tt, tl, Pull.S{Pull.MWord{[ch], 1, V.num.ok.step(V.NStart{}, Char.to_u32(ch))}, stack, Pull.GNext{},
        False{}, False{}}), hc)
    case Lex.Lex{Lex.Hi{+m1}, +bf, +tk}:
      M6.no(M4.sinv(tt, tl, Pull.S{Pull.MWord{[ch], 1, V.num.ok.step(V.NStart{}, Char.to_u32(ch))}, stack, Pull.GNext{},
        False{}, False{}}), hc)
    case Lex.Lex{Lex.HiEsc{+m1}, +bf, +tk}:
      M6.no(M4.sinv(tt, tl, Pull.S{Pull.MWord{[ch], 1, V.num.ok.step(V.NStart{}, Char.to_u32(ch))}, stack, Pull.GNext{},
        False{}, False{}}), hc)
    case Lex.Lex{Lex.Lo{+m1, +m2, +m3}, +bf, +tk}:
      M6.no(M4.sinv(tt, tl, Pull.S{Pull.MWord{[ch], 1, V.num.ok.step(V.NStart{}, Char.to_u32(ch))}, stack, Pull.GNext{},
        False{}, False{}}), hc)
    case Lex.Lex{Lex.Bad{}, +bf, +tk}:
      M6.no(M4.sinv(tt, tl, Pull.S{Pull.MWord{[ch], 1, V.num.ok.step(V.NStart{}, Char.to_u32(ch))}, stack, Pull.GNext{},
        False{}, False{}}), hc)

law idle_ot.at:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +stack: List<&2, Pull.Frame>
    for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for +lx: Lex.Lex
  for +e: M6.lx_e(tt, SCon{ch, tl}, lx)
  for +hc: {M6.cm(lx, SCon{ch, tl}) == True{} : Bool}
  for +hp: {M6.prel(stack, False{}, M6.pst(lx)) == True{} : Bool}
  for +ecls: {Lex.classify(ch) == Lex.COther{} : Lex.Class}
  for bb: Bool
  for +eb: {Pull.expect.val.go(stack) == bb : Bool}
  M4.sinv(tt, tl, Pull.look.word(ch, stack, Pull.GNext{}, False{}, Pull.expect.val.go(stack)))

def idle_ot.at(tt, ch, tl, stack, h_s, lx, e, hc, hp, ecls, bb, eb):
  match bb:
    case False{}:
      es = Equal.sym(Bool, Pull.expect.val.go(stack), False{}, eb)
      %es : M4.sinv(tt, tl, Pull.look.word(ch, stack, Pull.GNext{}, False{}, _))
      Unit{}
    case True{}:
      es = Equal.sym(Bool, Pull.expect.val.go(stack), True{}, eb)
      %es : M4.sinv(tt, tl, Pull.look.word(ch, stack, Pull.GNext{}, False{}, _))
      idle_ot.go(tt, ch, tl, stack, h_s, lx, e, hc, hp, ecls, eb)

law idle_cls:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +stack: List<&2, Pull.Frame>
  for done: Bool
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for +lx: Lex.Lex
  for +e: M6.lx_e(tt, SCon{ch, tl}, lx)
  for +hc: {M6.cm(lx, SCon{ch, tl}) == True{} : Bool}
  for +hp: {M6.prel(stack, done, M6.pst(lx)) == True{} : Bool}
  for cls: Lex.Class
  for +ecls: {Lex.classify(ch) == cls : Lex.Class}
  M4.sinv(tt, tl, Pull.look.plan(ch, stack, Pull.GNext{}, done, cls))

def idle_cls(tt, ch, tl, stack, done, h_s, lx, e, hc, hp, cls, ecls):
  match done:
    case True{}:
      match cls:
        case Lex.CSpace{}:
          (M2.short_tail(ch, tl, h_s), (Lex.Lex{Lex.Idle{}, [], M6.eff(lx)}, (Equal.trans(Lex.Lex,
            Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.feed(ch, lx)),
            Lex.run(String.to_list(tl), Lex.Lex{Lex.Idle{}, [], M6.eff(lx)}), e, Equal.cong(Lex.Lex, Lex.Lex,
            xx => Lex.run(String.to_list(tl), xx), Lex.feed(ch, lx), Lex.Lex{Lex.Idle{}, [], M6.eff(lx)}, feed_cls(ch,
                lx,
            tl, Lex.CSpace{}, ecls, hc, {==}))), ({==}, hp))))
        case Lex.CPunct{_}:
          Unit{}
        case Lex.CQuote{}:
          Unit{}
        case Lex.CBack{}:
          Unit{}
        case Lex.COther{}:
          Unit{}
    case False{}:
      match cls:
        case Lex.CSpace{}:
          (M2.short_tail(ch, tl, h_s), (Lex.Lex{Lex.Idle{}, [], M6.eff(lx)}, (Equal.trans(Lex.Lex,
            Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.feed(ch, lx)),
            Lex.run(String.to_list(tl), Lex.Lex{Lex.Idle{}, [], M6.eff(lx)}), e, Equal.cong(Lex.Lex, Lex.Lex,
            xx => Lex.run(String.to_list(tl), xx), Lex.feed(ch, lx), Lex.Lex{Lex.Idle{}, [], M6.eff(lx)}, feed_cls(ch,
                lx,
            tl, Lex.CSpace{}, ecls, hc, {==}))), ({==}, hp))))
        case Lex.CPunct{+tok}:
          idle_pu.at(tok, tt, ch, tl, stack, h_s, lx, e, hc, hp, M6.pst(lx), {==}, ecls)
        case Lex.CQuote{}:
          idle_qu.at(tt, ch, tl, stack, h_s, lx, e, hc, hp, ecls, Pull.expect.str.go(stack), {==})
        case Lex.CBack{}:
          Unit{}
        case Lex.COther{}:
          idle_ot.at(tt, ch, tl, stack, h_s, lx, e, hc, hp, ecls, Pull.expect.val.go(stack), {==})

# a quotation mark between tokens, once whether a string may start is named
# a word character between tokens, once whether a value may start is named
# a word character between tokens where a value may start: the word is open in both
# one character between tokens: the cursor fails or stays in step
law idle_go:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for hh: M6.cinv(tt, Pull.Cur{SCon{ch, tl}, stack, done, False{}})
  M4.sinv(tt, tl, Pull.look.plan(ch, stack, Pull.GNext{}, done, Lex.classify(ch)))

def idle_go(tt, ch, tl, stack, done, hh):
  (h_s, (+lx, (e, (hc, hp)))) = hh
  idle_cls(tt, ch, tl, stack, done, h_s, lx, e, hc, hp, Lex.classify(ch), {==})

# a string closed on the suffix in hand: a member's name, or a value where one may go
law land_here:
  for +tt: String
  for +tl: String
  for +lx: Lex.Lex
  for +ss: String
  for +stack: List<&2, Pull.Frame>
  for +pc: Pull.Piece
  for +qs: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +h_s: {D1.short(tl) == True{} : Bool}
  for +e: M6.lx_e(tt, tl, lx)
  for +hc: {M6.cm(lx, tl) == True{} : Bool}
  for +hp: {M6.prel(stack, False{}, Parse.P{False{}, root, qs}) == True{} : Bool}
  for +eq: {M6.pst(lx) == Parse.put.str(qs, root, Parse.KOwn{ss}, False{}) : Parse.P}
  M4.sinv(tt, tl, Pull.str.place.here(pc, stack, Pull.GNext{}))

def land_here(tt, tl, lx, ss, stack, pc, qs, root, h_s, e, hc, hp, eq):
  match stack:
    case Nil{}:
      match pc:
        case Pull.PSpan{+c1, +n1}:
          M4.land_c(tt, tl, lx, [], qs, root, V.JStr{ss}, h_s, e, hc, hp, {==}, Equal.trans(Parse.P, M6.pst(lx),
            Parse.put.str(qs, root, Parse.KOwn{ss}, False{}), Parse.put(qs, root, V.JStr{ss}, False{}), eq,
            ps_put([], qs, root, Parse.KOwn{ss}, hp, {==})))
        case Pull.POwn{+b1}:
          M4.land_c(tt, tl, lx, [], qs, root, V.JStr{ss}, h_s, e, hc, hp, {==}, Equal.trans(Parse.P, M6.pst(lx),
            Parse.put.str(qs, root, Parse.KOwn{ss}, False{}), Parse.put(qs, root, V.JStr{ss}, False{}), eq,
            ps_put([], qs, root, Parse.KOwn{ss}, hp, {==})))
    case Pull.FArr{Pull.SVal{}, +ff} <> +st:
      match pc:
        case Pull.PSpan{+c1, +n1}:
          M4.land_c(tt, tl, lx, Pull.FArr{Pull.SVal{}, ff} <> st, qs, root, V.JStr{ss}, h_s, e, hc, hp, {==},
            Equal.trans(Parse.P, M6.pst(lx),
            Parse.put.str(qs, root, Parse.KOwn{ss}, False{}), Parse.put(qs, root, V.JStr{ss}, False{}), eq,
            ps_put(Pull.FArr{Pull.SVal{}, ff} <> st, qs, root, Parse.KOwn{ss}, hp, {==})))
        case Pull.POwn{+b1}:
          M4.land_c(tt, tl, lx, Pull.FArr{Pull.SVal{}, ff} <> st, qs, root, V.JStr{ss}, h_s, e, hc, hp, {==},
            Equal.trans(Parse.P, M6.pst(lx),
            Parse.put.str(qs, root, Parse.KOwn{ss}, False{}), Parse.put(qs, root, V.JStr{ss}, False{}), eq,
            ps_put(Pull.FArr{Pull.SVal{}, ff} <> st, qs, root, Parse.KOwn{ss}, hp, {==})))
    case Pull.FArr{Pull.SCom{}, +ff} <> +st:
      Unit{}
    case Pull.FArr{Pull.SKey{}, +ff} <> +st:
      Unit{}
    case Pull.FArr{Pull.SCol{}, +ff} <> +st:
      Unit{}
    case Pull.FObj{Pull.SVal{}, +ff} <> +st:
      match pc:
        case Pull.PSpan{+c1, +n1}:
          M4.land_c(tt, tl, lx, Pull.FObj{Pull.SVal{}, ff} <> st, qs, root, V.JStr{ss}, h_s, e, hc, hp, {==},
            Equal.trans(Parse.P, M6.pst(lx),
            Parse.put.str(qs, root, Parse.KOwn{ss}, False{}), Parse.put(qs, root, V.JStr{ss}, False{}), eq,
            ps_put(Pull.FObj{Pull.SVal{}, ff} <> st, qs, root, Parse.KOwn{ss}, hp, {==})))
        case Pull.POwn{+b1}:
          M4.land_c(tt, tl, lx, Pull.FObj{Pull.SVal{}, ff} <> st, qs, root, V.JStr{ss}, h_s, e, hc, hp, {==},
            Equal.trans(Parse.P, M6.pst(lx),
            Parse.put.str(qs, root, Parse.KOwn{ss}, False{}), Parse.put(qs, root, V.JStr{ss}, False{}), eq,
            ps_put(Pull.FObj{Pull.SVal{}, ff} <> st, qs, root, Parse.KOwn{ss}, hp, {==})))
    case Pull.FObj{Pull.SCom{}, +ff} <> +st:
      Unit{}
    case Pull.FObj{Pull.SKey{}, +ff} <> +st:
      match pc:
        case Pull.PSpan{+c1, +n1}:
          match qs:
            case Nil{}:
              M6.no(M4.sinv(tt, tl, Pull.str.place.here(Pull.PSpan{c1, n1}, Pull.FObj{Pull.SKey{}, ff} <> st,
                  Pull.GNext{})),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st), M6.frels(Pull.FObj{Pull.SKey{},
                ff} <> st, []), hp))
            case Parse.FArr{+items, Parse.SValue{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place.here(Pull.PSpan{c1, n1}, Pull.FObj{Pull.SKey{}, ff} <> st,
                  Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt)), hp)))
            case Parse.FArr{+items, Parse.SComma{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place.here(Pull.PSpan{c1, n1}, Pull.FObj{Pull.SKey{}, ff} <> st,
                  Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt)), hp)))
            case Parse.FArr{+items, Parse.SKey{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place.here(Pull.PSpan{c1, n1}, Pull.FObj{Pull.SKey{}, ff} <> st,
                  Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt)), hp)))
            case Parse.FArr{+items, Parse.SColon{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place.here(Pull.PSpan{c1, n1}, Pull.FObj{Pull.SKey{}, ff} <> st,
                  Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt)), hp)))
            case Parse.FObj{+items, +kk, Parse.SValue{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place.here(Pull.PSpan{c1, n1}, Pull.FObj{Pull.SKey{}, ff} <> st,
                  Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st,
                    qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt)), hp)))
            case Parse.FObj{+items, +kk, Parse.SComma{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place.here(Pull.PSpan{c1, n1}, Pull.FObj{Pull.SKey{}, ff} <> st,
                  Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st,
                    qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st, qt)), hp)))
            case Parse.FObj{+items, +kk, Parse.SKey{}} <> +qt:
              match root:
                case None{}:
                  (h_s, (lx, (e, (hc, Equal.trans(Bool, M6.prel(Pull.FObj{Pull.SCol{}, False{}} <> st, False{},
                      M6.pst(lx)),
                    M6.prel(Pull.FObj{Pull.SCol{}, False{}} <> st, False{}, Parse.P{False{}, None{}, Parse.FObj{items,
                      Parse.KOwn{ss}, Parse.SColon{}} <> qt}), True{},
                    Equal.cong(Parse.P, Bool, xx => M6.prel(Pull.FObj{Pull.SCol{}, False{}} <> st, False{}, xx),
                        M6.pst(lx),
                    Parse.P{False{}, None{}, Parse.FObj{items, Parse.KOwn{ss}, Parse.SColon{}} <> qt}, eq),
                      M6.and_right(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SKey{}}),
                          M6.frels(st, qt),
                      M6.and_right(M6.rrel(False{}, None{}, Pull.FObj{Pull.SKey{}, ff} <> st),
                      Bool.and(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st,
                          qt)),
                      hp)))))))
                case Some{+rv}:
                  M6.no(M4.sinv(tt, tl, Pull.str.place.here(Pull.PSpan{c1, n1}, Pull.FObj{Pull.SKey{}, ff} <> st,
                    Pull.GNext{})), M6.and_left(M6.rrel(False{}, Some{rv}, Pull.FObj{Pull.SKey{}, ff} <> st),
                    M6.frels(Pull.FObj{Pull.SKey{}, ff} <> st, Parse.FObj{items, kk, Parse.SKey{}} <> qt), hp))
            case Parse.FObj{+items, +kk, Parse.SColon{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place.here(Pull.PSpan{c1, n1}, Pull.FObj{Pull.SKey{}, ff} <> st,
                  Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st,
                    qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt)), hp)))
        case Pull.POwn{+b1}:
          match qs:
            case Nil{}:
              M6.no(M4.sinv(tt, tl, Pull.str.place.here(Pull.POwn{b1}, Pull.FObj{Pull.SKey{}, ff} <> st, Pull.GNext{})),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st), M6.frels(Pull.FObj{Pull.SKey{},
                ff} <> st, []), hp))
            case Parse.FArr{+items, Parse.SValue{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place.here(Pull.POwn{b1}, Pull.FObj{Pull.SKey{}, ff} <> st, Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt)), hp)))
            case Parse.FArr{+items, Parse.SComma{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place.here(Pull.POwn{b1}, Pull.FObj{Pull.SKey{}, ff} <> st, Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt)), hp)))
            case Parse.FArr{+items, Parse.SKey{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place.here(Pull.POwn{b1}, Pull.FObj{Pull.SKey{}, ff} <> st, Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt)), hp)))
            case Parse.FArr{+items, Parse.SColon{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place.here(Pull.POwn{b1}, Pull.FObj{Pull.SKey{}, ff} <> st, Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt)), hp)))
            case Parse.FObj{+items, +kk, Parse.SValue{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place.here(Pull.POwn{b1}, Pull.FObj{Pull.SKey{}, ff} <> st, Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st,
                    qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt)), hp)))
            case Parse.FObj{+items, +kk, Parse.SComma{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place.here(Pull.POwn{b1}, Pull.FObj{Pull.SKey{}, ff} <> st, Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st,
                    qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st, qt)), hp)))
            case Parse.FObj{+items, +kk, Parse.SKey{}} <> +qt:
              match root:
                case None{}:
                  (h_s, (lx, (e, (hc, Equal.trans(Bool, M6.prel(Pull.FObj{Pull.SCol{}, False{}} <> st, False{},
                      M6.pst(lx)),
                    M6.prel(Pull.FObj{Pull.SCol{}, False{}} <> st, False{}, Parse.P{False{}, None{}, Parse.FObj{items,
                      Parse.KOwn{ss}, Parse.SColon{}} <> qt}), True{},
                    Equal.cong(Parse.P, Bool, xx => M6.prel(Pull.FObj{Pull.SCol{}, False{}} <> st, False{}, xx),
                        M6.pst(lx),
                    Parse.P{False{}, None{}, Parse.FObj{items, Parse.KOwn{ss}, Parse.SColon{}} <> qt}, eq),
                      M6.and_right(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SKey{}}),
                          M6.frels(st, qt),
                      M6.and_right(M6.rrel(False{}, None{}, Pull.FObj{Pull.SKey{}, ff} <> st),
                      Bool.and(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st,
                          qt)),
                      hp)))))))
                case Some{+rv}:
                  M6.no(M4.sinv(tt, tl, Pull.str.place.here(Pull.POwn{b1}, Pull.FObj{Pull.SKey{}, ff} <> st,
                      Pull.GNext{})),
                    M6.and_left(M6.rrel(False{}, Some{rv}, Pull.FObj{Pull.SKey{}, ff} <> st),
                        M6.frels(Pull.FObj{Pull.SKey{},
                    ff} <> st, Parse.FObj{items, kk, Parse.SKey{}} <> qt), hp))
            case Parse.FObj{+items, +kk, Parse.SColon{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place.here(Pull.POwn{b1}, Pull.FObj{Pull.SKey{}, ff} <> st, Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st,
                    qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt)), hp)))
    case Pull.FObj{Pull.SCol{}, +ff} <> +st:
      Unit{}

# a string closed after its decoded characters: a member's name, or a value where one may go
law land_own:
  for +tt: String
  for +tl: String
  for +lx: Lex.Lex
  for +ss: String
  for +stack: List<&2, Pull.Frame>
  for +pc: Pull.Piece
  for +qs: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +h_s: {D1.short(tl) == True{} : Bool}
  for +e: M6.lx_e(tt, tl, lx)
  for +hc: {M6.cm(lx, tl) == True{} : Bool}
  for +hp: {M6.prel(stack, False{}, Parse.P{False{}, root, qs}) == True{} : Bool}
  for +eq: {M6.pst(lx) == Parse.put.str(qs, root, Parse.KOwn{ss}, False{}) : Parse.P}
  M4.sinv(tt, tl, Pull.str.place(pc, tl, stack, Pull.GNext{}))

def land_own(tt, tl, lx, ss, stack, pc, qs, root, h_s, e, hc, hp, eq):
  match stack:
    case Nil{}:
      match pc:
        case Pull.PSpan{+c1, +n1}:
          M4.land_c(tt, tl, lx, [], qs, root, V.JStr{ss}, h_s, e, hc, hp, {==}, Equal.trans(Parse.P, M6.pst(lx),
            Parse.put.str(qs, root, Parse.KOwn{ss}, False{}), Parse.put(qs, root, V.JStr{ss}, False{}), eq,
            ps_put([], qs, root, Parse.KOwn{ss}, hp, {==})))
        case Pull.POwn{+b1}:
          M4.land_c(tt, tl, lx, [], qs, root, V.JStr{ss}, h_s, e, hc, hp, {==}, Equal.trans(Parse.P, M6.pst(lx),
            Parse.put.str(qs, root, Parse.KOwn{ss}, False{}), Parse.put(qs, root, V.JStr{ss}, False{}), eq,
            ps_put([], qs, root, Parse.KOwn{ss}, hp, {==})))
    case Pull.FArr{Pull.SVal{}, +ff} <> +st:
      match pc:
        case Pull.PSpan{+c1, +n1}:
          M4.land_c(tt, tl, lx, Pull.FArr{Pull.SVal{}, ff} <> st, qs, root, V.JStr{ss}, h_s, e, hc, hp, {==},
            Equal.trans(Parse.P, M6.pst(lx),
            Parse.put.str(qs, root, Parse.KOwn{ss}, False{}), Parse.put(qs, root, V.JStr{ss}, False{}), eq,
            ps_put(Pull.FArr{Pull.SVal{}, ff} <> st, qs, root, Parse.KOwn{ss}, hp, {==})))
        case Pull.POwn{+b1}:
          M4.land_c(tt, tl, lx, Pull.FArr{Pull.SVal{}, ff} <> st, qs, root, V.JStr{ss}, h_s, e, hc, hp, {==},
            Equal.trans(Parse.P, M6.pst(lx),
            Parse.put.str(qs, root, Parse.KOwn{ss}, False{}), Parse.put(qs, root, V.JStr{ss}, False{}), eq,
            ps_put(Pull.FArr{Pull.SVal{}, ff} <> st, qs, root, Parse.KOwn{ss}, hp, {==})))
    case Pull.FArr{Pull.SCom{}, +ff} <> +st:
      Unit{}
    case Pull.FArr{Pull.SKey{}, +ff} <> +st:
      Unit{}
    case Pull.FArr{Pull.SCol{}, +ff} <> +st:
      Unit{}
    case Pull.FObj{Pull.SVal{}, +ff} <> +st:
      match pc:
        case Pull.PSpan{+c1, +n1}:
          M4.land_c(tt, tl, lx, Pull.FObj{Pull.SVal{}, ff} <> st, qs, root, V.JStr{ss}, h_s, e, hc, hp, {==},
            Equal.trans(Parse.P, M6.pst(lx),
            Parse.put.str(qs, root, Parse.KOwn{ss}, False{}), Parse.put(qs, root, V.JStr{ss}, False{}), eq,
            ps_put(Pull.FObj{Pull.SVal{}, ff} <> st, qs, root, Parse.KOwn{ss}, hp, {==})))
        case Pull.POwn{+b1}:
          M4.land_c(tt, tl, lx, Pull.FObj{Pull.SVal{}, ff} <> st, qs, root, V.JStr{ss}, h_s, e, hc, hp, {==},
            Equal.trans(Parse.P, M6.pst(lx),
            Parse.put.str(qs, root, Parse.KOwn{ss}, False{}), Parse.put(qs, root, V.JStr{ss}, False{}), eq,
            ps_put(Pull.FObj{Pull.SVal{}, ff} <> st, qs, root, Parse.KOwn{ss}, hp, {==})))
    case Pull.FObj{Pull.SCom{}, +ff} <> +st:
      Unit{}
    case Pull.FObj{Pull.SKey{}, +ff} <> +st:
      match pc:
        case Pull.PSpan{+c1, +n1}:
          match qs:
            case Nil{}:
              M6.no(M4.sinv(tt, tl, Pull.str.place(Pull.PSpan{c1, n1}, tl, Pull.FObj{Pull.SKey{}, ff} <> st,
                  Pull.GNext{})),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st), M6.frels(Pull.FObj{Pull.SKey{},
                ff} <> st, []), hp))
            case Parse.FArr{+items, Parse.SValue{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place(Pull.PSpan{c1, n1}, tl, Pull.FObj{Pull.SKey{}, ff} <> st,
                  Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt)), hp)))
            case Parse.FArr{+items, Parse.SComma{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place(Pull.PSpan{c1, n1}, tl, Pull.FObj{Pull.SKey{}, ff} <> st,
                  Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt)), hp)))
            case Parse.FArr{+items, Parse.SKey{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place(Pull.PSpan{c1, n1}, tl, Pull.FObj{Pull.SKey{}, ff} <> st,
                  Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt)), hp)))
            case Parse.FArr{+items, Parse.SColon{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place(Pull.PSpan{c1, n1}, tl, Pull.FObj{Pull.SKey{}, ff} <> st,
                  Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt)), hp)))
            case Parse.FObj{+items, +kk, Parse.SValue{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place(Pull.PSpan{c1, n1}, tl, Pull.FObj{Pull.SKey{}, ff} <> st,
                  Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st,
                    qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt)), hp)))
            case Parse.FObj{+items, +kk, Parse.SComma{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place(Pull.PSpan{c1, n1}, tl, Pull.FObj{Pull.SKey{}, ff} <> st,
                  Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st,
                    qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st, qt)), hp)))
            case Parse.FObj{+items, +kk, Parse.SKey{}} <> +qt:
              match root:
                case None{}:
                  (h_s, (lx, (e, (hc, Equal.trans(Bool, M6.prel(Pull.FObj{Pull.SCol{}, False{}} <> st, False{},
                      M6.pst(lx)),
                    M6.prel(Pull.FObj{Pull.SCol{}, False{}} <> st, False{}, Parse.P{False{}, None{}, Parse.FObj{items,
                      Parse.KOwn{ss}, Parse.SColon{}} <> qt}), True{},
                    Equal.cong(Parse.P, Bool, xx => M6.prel(Pull.FObj{Pull.SCol{}, False{}} <> st, False{}, xx),
                        M6.pst(lx),
                    Parse.P{False{}, None{}, Parse.FObj{items, Parse.KOwn{ss}, Parse.SColon{}} <> qt}, eq),
                      M6.and_right(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SKey{}}),
                          M6.frels(st, qt),
                      M6.and_right(M6.rrel(False{}, None{}, Pull.FObj{Pull.SKey{}, ff} <> st),
                      Bool.and(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st,
                          qt)),
                      hp)))))))
                case Some{+rv}:
                  M6.no(M4.sinv(tt, tl, Pull.str.place(Pull.PSpan{c1, n1}, tl, Pull.FObj{Pull.SKey{}, ff} <> st,
                    Pull.GNext{})), M6.and_left(M6.rrel(False{}, Some{rv}, Pull.FObj{Pull.SKey{}, ff} <> st),
                    M6.frels(Pull.FObj{Pull.SKey{}, ff} <> st, Parse.FObj{items, kk, Parse.SKey{}} <> qt), hp))
            case Parse.FObj{+items, +kk, Parse.SColon{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place(Pull.PSpan{c1, n1}, tl, Pull.FObj{Pull.SKey{}, ff} <> st,
                  Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st,
                    qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt)), hp)))
        case Pull.POwn{+b1}:
          match qs:
            case Nil{}:
              M6.no(M4.sinv(tt, tl, Pull.str.place(Pull.POwn{b1}, tl, Pull.FObj{Pull.SKey{}, ff} <> st, Pull.GNext{})),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st), M6.frels(Pull.FObj{Pull.SKey{},
                ff} <> st, []), hp))
            case Parse.FArr{+items, Parse.SValue{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place(Pull.POwn{b1}, tl, Pull.FObj{Pull.SKey{}, ff} <> st, Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FArr{items, Parse.SValue{}}), M6.frels(st, qt)), hp)))
            case Parse.FArr{+items, Parse.SComma{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place(Pull.POwn{b1}, tl, Pull.FObj{Pull.SKey{}, ff} <> st, Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FArr{items, Parse.SComma{}}), M6.frels(st, qt)), hp)))
            case Parse.FArr{+items, Parse.SKey{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place(Pull.POwn{b1}, tl, Pull.FObj{Pull.SKey{}, ff} <> st, Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FArr{items, Parse.SKey{}}), M6.frels(st, qt)), hp)))
            case Parse.FArr{+items, Parse.SColon{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place(Pull.POwn{b1}, tl, Pull.FObj{Pull.SKey{}, ff} <> st, Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FArr{items, Parse.SColon{}}), M6.frels(st, qt)), hp)))
            case Parse.FObj{+items, +kk, Parse.SValue{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place(Pull.POwn{b1}, tl, Pull.FObj{Pull.SKey{}, ff} <> st, Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st,
                    qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FObj{items, kk, Parse.SValue{}}), M6.frels(st, qt)), hp)))
            case Parse.FObj{+items, +kk, Parse.SComma{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place(Pull.POwn{b1}, tl, Pull.FObj{Pull.SKey{}, ff} <> st, Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st,
                    qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FObj{items, kk, Parse.SComma{}}), M6.frels(st, qt)), hp)))
            case Parse.FObj{+items, +kk, Parse.SKey{}} <> +qt:
              match root:
                case None{}:
                  (h_s, (lx, (e, (hc, Equal.trans(Bool, M6.prel(Pull.FObj{Pull.SCol{}, False{}} <> st, False{},
                      M6.pst(lx)),
                    M6.prel(Pull.FObj{Pull.SCol{}, False{}} <> st, False{}, Parse.P{False{}, None{}, Parse.FObj{items,
                      Parse.KOwn{ss}, Parse.SColon{}} <> qt}), True{},
                    Equal.cong(Parse.P, Bool, xx => M6.prel(Pull.FObj{Pull.SCol{}, False{}} <> st, False{}, xx),
                        M6.pst(lx),
                    Parse.P{False{}, None{}, Parse.FObj{items, Parse.KOwn{ss}, Parse.SColon{}} <> qt}, eq),
                      M6.and_right(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SKey{}}),
                          M6.frels(st, qt),
                      M6.and_right(M6.rrel(False{}, None{}, Pull.FObj{Pull.SKey{}, ff} <> st),
                      Bool.and(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SKey{}}), M6.frels(st,
                          qt)),
                      hp)))))))
                case Some{+rv}:
                  M6.no(M4.sinv(tt, tl, Pull.str.place(Pull.POwn{b1}, tl, Pull.FObj{Pull.SKey{}, ff} <> st,
                      Pull.GNext{})),
                    M6.and_left(M6.rrel(False{}, Some{rv}, Pull.FObj{Pull.SKey{}, ff} <> st),
                        M6.frels(Pull.FObj{Pull.SKey{},
                    ff} <> st, Parse.FObj{items, kk, Parse.SKey{}} <> qt), hp))
            case Parse.FObj{+items, +kk, Parse.SColon{}} <> +qt:
              M6.no(M4.sinv(tt, tl, Pull.str.place(Pull.POwn{b1}, tl, Pull.FObj{Pull.SKey{}, ff} <> st, Pull.GNext{})),
                M6.and_left(M6.frel(Pull.FObj{Pull.SKey{}, ff}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st,
                    qt),
                M6.and_right(M6.rrel(False{}, root, Pull.FObj{Pull.SKey{}, ff} <> st),
                    Bool.and(M6.frel(Pull.FObj{Pull.SKey{},
                ff}, Parse.FObj{items, kk, Parse.SColon{}}), M6.frels(st, qt)), hp)))
    case Pull.FObj{Pull.SCol{}, +ff} <> +st:
      Unit{}

# laws/CursorEventsMatchParse.bend, strings in step with the lexer

# the lexer's state, its mode rewritten
law lxfix_e:
  for +tt: String
  for +xx: String
  for +md: Lex.Mode
  for +md2: Lex.Mode
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for hm: {md == md2 : Lex.Mode}
  for e: M6.lx_e(tt, xx, Lex.Lex{md, bf, tk})
  M6.lx_e(tt, xx, Lex.Lex{md2, bf, tk})

def lxfix_e(tt, xx, md, md2, bf, tk, hm, e):
  Equal.trans(Lex.Lex, Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(xx), Lex.Lex{md, bf, tk}),
    Lex.run(String.to_list(xx), Lex.Lex{md2, bf, tk}), e, Equal.cong(Lex.Mode, Lex.Lex,
      zz => Lex.run(String.to_list(xx), Lex.Lex{zz, bf, tk}), md, md2, hm))

# the parser after a lexer state, its mode rewritten
law lxfix_p:
  for +stack: List<&2, Pull.Frame>
  for +md: Lex.Mode
  for +md2: Lex.Mode
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for hm: {md == md2 : Lex.Mode}
  for hp: {M6.prel(stack, False{}, M6.pst(Lex.Lex{md, bf, tk})) == True{} : Bool}
  {M6.prel(stack, False{}, M6.pst(Lex.Lex{md2, bf, tk})) == True{} : Bool}

def lxfix_p(stack, md, md2, bf, tk, hm, hp):
  Equal.trans(Bool, M6.prel(stack, False{}, M6.pst(Lex.Lex{md2, bf, tk})), M6.prel(stack, False{}, M6.pst(Lex.Lex{md,
      bf, tk})),
    True{}, Equal.sym(Bool, M6.prel(stack, False{}, M6.pst(Lex.Lex{md, bf, tk})), M6.prel(stack, False{},
        M6.pst(Lex.Lex{md2, bf,
    tk})), Equal.cong(Lex.Mode, Bool, zz => M6.prel(stack, False{}, M6.pst(Lex.Lex{zz, bf, tk})), md, md2, hm)), hp)

# ss_copy
law ss_copy:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for +e: M6.lx_e(tt, SCon{ch, tl}, Lex.Lex{Lex.Str{}, bf, tk})
  for +hp: {M6.prel(stack, False{}, M6.pst(Lex.Lex{Lex.Str{}, bf, tk})) == True{} : Bool}
  for cls: Lex.Class
  for +ecls: {Lex.classify(ch) == cls : Lex.Class}
  for ctl: Bool
  for +ect: {U32.is_lt(Char.to_u32(ch), 32) == ctl : Bool}
  M4.sinv(tt, tl, Pull.copy.hit.go(ch, tl, buf, stack, Pull.GNext{}, False{}, cls, ctl))

def ss_copy(tt, ch, tl, buf, stack, bf, tk, h_s, e, hp, cls, ecls, ctl, ect):
  match cls:
    case Lex.CQuote{}:
      match ctl:
        case True{}:
          M4.pp_split(M4.sinv(tt, tl, Pull.copy.hit.go(ch, tl, buf, stack, Pull.GNext{}, False{}, Lex.CQuote{},
              True{})),
            M6.pst(Lex.Lex{Lex.Str{}, bf, tk}), stack, hp, +root => +qs => hp2 => epp => land_own(tt, tl,
            M4.lxi(Lex.TStr{Lex.text(bf)} <> tk), Lex.text(bf), stack, Pull.POwn{Lex.text(buf)}, qs, root,
                M2.short_tail(ch,
            tl, h_s), Equal.trans(Lex.Lex, Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl),
            Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk)), Lex.run(String.to_list(tl),
            M4.lxi(Lex.TStr{Lex.text(bf)} <> tk)), e, Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list(tl),
                zz),
            Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk), M4.lxi(Lex.TStr{Lex.text(bf)} <> tk),
                Equal.cong(Lex.Class,
            Lex.Lex, zz => Lex.step(Lex.Str{}, zz, ch, bf, tk), Lex.classify(ch), Lex.CQuote{}, ecls))), {==}, hp2,
            Equal.trans(Parse.P, M6.pst(M4.lxi(Lex.TStr{Lex.text(bf)} <> tk)), Parse.step(Lex.TStr{Lex.text(bf)},
            M6.pst(Lex.Lex{Lex.Str{}, bf, tk})), Parse.step(Lex.TStr{Lex.text(bf)}, Parse.P{False{}, root, qs}),
            M4.pst_push(Lex.TStr{Lex.text(bf)}, tk), Equal.cong(Parse.P, Parse.P,
                zz => Parse.step(Lex.TStr{Lex.text(bf)},
            zz), M6.pst(Lex.Lex{Lex.Str{}, bf, tk}), Parse.P{False{}, root, qs}, epp))))
        case False{}:
          M4.pp_split(M4.sinv(tt, tl, Pull.copy.hit.go(ch, tl, buf, stack, Pull.GNext{}, False{}, Lex.CQuote{},
              False{})),
            M6.pst(Lex.Lex{Lex.Str{}, bf, tk}), stack, hp, +root => +qs => hp2 => epp => land_own(tt, tl,
            M4.lxi(Lex.TStr{Lex.text(bf)} <> tk), Lex.text(bf), stack, Pull.POwn{Lex.text(buf)}, qs, root,
                M2.short_tail(ch,
            tl, h_s), Equal.trans(Lex.Lex, Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl),
            Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk)), Lex.run(String.to_list(tl),
            M4.lxi(Lex.TStr{Lex.text(bf)} <> tk)), e, Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list(tl),
                zz),
            Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk), M4.lxi(Lex.TStr{Lex.text(bf)} <> tk),
                Equal.cong(Lex.Class,
            Lex.Lex, zz => Lex.step(Lex.Str{}, zz, ch, bf, tk), Lex.classify(ch), Lex.CQuote{}, ecls))), {==}, hp2,
            Equal.trans(Parse.P, M6.pst(M4.lxi(Lex.TStr{Lex.text(bf)} <> tk)), Parse.step(Lex.TStr{Lex.text(bf)},
            M6.pst(Lex.Lex{Lex.Str{}, bf, tk})), Parse.step(Lex.TStr{Lex.text(bf)}, Parse.P{False{}, root, qs}),
            M4.pst_push(Lex.TStr{Lex.text(bf)}, tk), Equal.cong(Parse.P, Parse.P,
                zz => Parse.step(Lex.TStr{Lex.text(bf)},
            zz), M6.pst(Lex.Lex{Lex.Str{}, bf, tk}), Parse.P{False{}, root, qs}, epp))))
    case Lex.CBack{}:
      match ctl:
        case True{}:
          Unit{}
        case False{}:
          (M2.short_tail(ch, tl, h_s), ({==}, (Lex.Lex{Lex.Esc{}, bf, tk}, (Equal.trans(Lex.Lex,
            Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.step(Lex.Str{}, Lex.classify(ch), ch,
            bf, tk)), Lex.run(String.to_list(tl), Lex.Lex{Lex.Esc{}, bf, tk}), e, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list(tl), zz), Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.Lex{Lex.Esc{}, bf, tk}, Equal.cong(Lex.Class, Lex.Lex, zz => Lex.step(Lex.Str{}, zz, ch, bf, tk),
            Lex.classify(ch), Lex.CBack{}, ecls))), ({==}, hp)))))
    case Lex.CPunct{+pt}:
      match ctl:
        case True{}:
          Unit{}
        case False{}:
          (M2.short_tail(ch, tl, h_s), ({==}, (Lex.Lex{Lex.Str{}, ch <> bf, tk}, (Equal.trans(Lex.Lex,
            Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.step(Lex.Str{}, Lex.classify(ch), ch,
            bf, tk)), Lex.run(String.to_list(tl), Lex.Lex{Lex.Str{}, ch <> bf, tk}), e, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list(tl), zz), Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.Lex{Lex.Str{}, ch <> bf, tk}, Equal.trans(Lex.Lex, Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.step.str.go(ch, bf, tk, U32.is_lt(Char.to_u32(ch), 32)), Lex.Lex{Lex.Str{}, ch <> bf, tk},
            Equal.cong(Lex.Class, Lex.Lex, zz => Lex.step(Lex.Str{}, zz, ch, bf, tk), Lex.classify(ch), Lex.CPunct{pt},
            ecls), Equal.cong(Bool, Lex.Lex, zz => Lex.step.str.go(ch, bf, tk, zz), U32.is_lt(Char.to_u32(ch), 32),
            False{}, ect)))), ({==}, hp)))))
    case Lex.CSpace{}:
      match ctl:
        case True{}:
          Unit{}
        case False{}:
          (M2.short_tail(ch, tl, h_s), ({==}, (Lex.Lex{Lex.Str{}, ch <> bf, tk}, (Equal.trans(Lex.Lex,
            Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.step(Lex.Str{}, Lex.classify(ch), ch,
            bf, tk)), Lex.run(String.to_list(tl), Lex.Lex{Lex.Str{}, ch <> bf, tk}), e, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list(tl), zz), Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.Lex{Lex.Str{}, ch <> bf, tk}, Equal.trans(Lex.Lex, Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.step.str.go(ch, bf, tk, U32.is_lt(Char.to_u32(ch), 32)), Lex.Lex{Lex.Str{}, ch <> bf, tk},
            Equal.cong(Lex.Class, Lex.Lex, zz => Lex.step(Lex.Str{}, zz, ch, bf, tk), Lex.classify(ch), Lex.CSpace{},
            ecls), Equal.cong(Bool, Lex.Lex, zz => Lex.step.str.go(ch, bf, tk, zz), U32.is_lt(Char.to_u32(ch), 32),
            False{}, ect)))), ({==}, hp)))))
    case Lex.COther{}:
      match ctl:
        case True{}:
          Unit{}
        case False{}:
          (M2.short_tail(ch, tl, h_s), ({==}, (Lex.Lex{Lex.Str{}, ch <> bf, tk}, (Equal.trans(Lex.Lex,
            Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.step(Lex.Str{}, Lex.classify(ch), ch,
            bf, tk)), Lex.run(String.to_list(tl), Lex.Lex{Lex.Str{}, ch <> bf, tk}), e, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list(tl), zz), Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.Lex{Lex.Str{}, ch <> bf, tk}, Equal.trans(Lex.Lex, Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.step.str.go(ch, bf, tk, U32.is_lt(Char.to_u32(ch), 32)), Lex.Lex{Lex.Str{}, ch <> bf, tk},
            Equal.cong(Lex.Class, Lex.Lex, zz => Lex.step(Lex.Str{}, zz, ch, bf, tk), Lex.classify(ch), Lex.COther{},
            ecls), Equal.cong(Bool, Lex.Lex, zz => Lex.step.str.go(ch, bf, tk, zz), U32.is_lt(Char.to_u32(ch), 32),
            False{}, ect)))), ({==}, hp)))))

# ss_span
law ss_span:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +cut: String
  for +nn: U32
  for +stack: List<&2, Pull.Frame>
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for +e: M6.lx_e(tt, SCon{ch, tl}, Lex.Lex{Lex.Str{}, bf, tk})
  for +hp: {M6.prel(stack, False{}, M6.pst(Lex.Lex{Lex.Str{}, bf, tk})) == True{} : Bool}
  for cls: Lex.Class
  for +ecls: {Lex.classify(ch) == cls : Lex.Class}
  for ctl: Bool
  for +ect: {U32.is_lt(Char.to_u32(ch), 32) == ctl : Bool}
  M4.sinv(tt, tl, Pull.span.advance(Pull.span.kind(cls, ctl), cut, nn, stack, Pull.GNext{}, False{}))

def ss_span(tt, ch, tl, cut, nn, stack, bf, tk, h_s, e, hp, cls, ecls, ctl, ect):
  match cls:
    case Lex.CQuote{}:
      match ctl:
        case True{}:
          M4.pp_split(M4.sinv(tt, tl, Pull.span.advance(Pull.span.kind(Lex.CQuote{}, True{}), cut, nn, stack,
              Pull.GNext{},
            False{})), M6.pst(Lex.Lex{Lex.Str{}, bf, tk}), stack, hp, +root => +qs => hp2 => epp => land_here(tt, tl,
            M4.lxi(Lex.TStr{Lex.text(bf)} <> tk), Lex.text(bf), stack, Pull.PSpan{cut, nn}, qs, root, M2.short_tail(ch,
                tl,
            h_s), Equal.trans(Lex.Lex, Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl),
            Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk)), Lex.run(String.to_list(tl),
            M4.lxi(Lex.TStr{Lex.text(bf)} <> tk)), e, Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list(tl),
                zz),
            Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk), M4.lxi(Lex.TStr{Lex.text(bf)} <> tk),
                Equal.cong(Lex.Class,
            Lex.Lex, zz => Lex.step(Lex.Str{}, zz, ch, bf, tk), Lex.classify(ch), Lex.CQuote{}, ecls))), {==}, hp2,
            Equal.trans(Parse.P, M6.pst(M4.lxi(Lex.TStr{Lex.text(bf)} <> tk)), Parse.step(Lex.TStr{Lex.text(bf)},
            M6.pst(Lex.Lex{Lex.Str{}, bf, tk})), Parse.step(Lex.TStr{Lex.text(bf)}, Parse.P{False{}, root, qs}),
            M4.pst_push(Lex.TStr{Lex.text(bf)}, tk), Equal.cong(Parse.P, Parse.P,
                zz => Parse.step(Lex.TStr{Lex.text(bf)},
            zz), M6.pst(Lex.Lex{Lex.Str{}, bf, tk}), Parse.P{False{}, root, qs}, epp))))
        case False{}:
          M4.pp_split(M4.sinv(tt, tl, Pull.span.advance(Pull.span.kind(Lex.CQuote{}, False{}), cut, nn, stack,
              Pull.GNext{},
            False{})), M6.pst(Lex.Lex{Lex.Str{}, bf, tk}), stack, hp, +root => +qs => hp2 => epp => land_here(tt, tl,
            M4.lxi(Lex.TStr{Lex.text(bf)} <> tk), Lex.text(bf), stack, Pull.PSpan{cut, nn}, qs, root, M2.short_tail(ch,
                tl,
            h_s), Equal.trans(Lex.Lex, Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl),
            Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk)), Lex.run(String.to_list(tl),
            M4.lxi(Lex.TStr{Lex.text(bf)} <> tk)), e, Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list(tl),
                zz),
            Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk), M4.lxi(Lex.TStr{Lex.text(bf)} <> tk),
                Equal.cong(Lex.Class,
            Lex.Lex, zz => Lex.step(Lex.Str{}, zz, ch, bf, tk), Lex.classify(ch), Lex.CQuote{}, ecls))), {==}, hp2,
            Equal.trans(Parse.P, M6.pst(M4.lxi(Lex.TStr{Lex.text(bf)} <> tk)), Parse.step(Lex.TStr{Lex.text(bf)},
            M6.pst(Lex.Lex{Lex.Str{}, bf, tk})), Parse.step(Lex.TStr{Lex.text(bf)}, Parse.P{False{}, root, qs}),
            M4.pst_push(Lex.TStr{Lex.text(bf)}, tk), Equal.cong(Parse.P, Parse.P,
                zz => Parse.step(Lex.TStr{Lex.text(bf)},
            zz), M6.pst(Lex.Lex{Lex.Str{}, bf, tk}), Parse.P{False{}, root, qs}, epp))))
    case Lex.CBack{}:
      match ctl:
        case True{}:
          Unit{}
        case False{}:
          (M2.short_tail(ch, tl, h_s), ({==}, (Lex.Lex{Lex.Esc{}, bf, tk}, (Equal.trans(Lex.Lex,
            Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.step(Lex.Str{}, Lex.classify(ch), ch,
            bf, tk)), Lex.run(String.to_list(tl), Lex.Lex{Lex.Esc{}, bf, tk}), e, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list(tl), zz), Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.Lex{Lex.Esc{}, bf, tk}, Equal.cong(Lex.Class, Lex.Lex, zz => Lex.step(Lex.Str{}, zz, ch, bf, tk),
            Lex.classify(ch), Lex.CBack{}, ecls))), ({==}, hp)))))
    case Lex.CPunct{+pt}:
      match ctl:
        case True{}:
          Unit{}
        case False{}:
          (M2.short_tail(ch, tl, h_s), ({==}, (Lex.Lex{Lex.Str{}, ch <> bf, tk}, (Equal.trans(Lex.Lex,
            Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.step(Lex.Str{}, Lex.classify(ch), ch,
            bf, tk)), Lex.run(String.to_list(tl), Lex.Lex{Lex.Str{}, ch <> bf, tk}), e, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list(tl), zz), Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.Lex{Lex.Str{}, ch <> bf, tk}, Equal.trans(Lex.Lex, Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.step.str.go(ch, bf, tk, U32.is_lt(Char.to_u32(ch), 32)), Lex.Lex{Lex.Str{}, ch <> bf, tk},
            Equal.cong(Lex.Class, Lex.Lex, zz => Lex.step(Lex.Str{}, zz, ch, bf, tk), Lex.classify(ch), Lex.CPunct{pt},
            ecls), Equal.cong(Bool, Lex.Lex, zz => Lex.step.str.go(ch, bf, tk, zz), U32.is_lt(Char.to_u32(ch), 32),
            False{}, ect)))), ({==}, hp)))))
    case Lex.CSpace{}:
      match ctl:
        case True{}:
          Unit{}
        case False{}:
          (M2.short_tail(ch, tl, h_s), ({==}, (Lex.Lex{Lex.Str{}, ch <> bf, tk}, (Equal.trans(Lex.Lex,
            Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.step(Lex.Str{}, Lex.classify(ch), ch,
            bf, tk)), Lex.run(String.to_list(tl), Lex.Lex{Lex.Str{}, ch <> bf, tk}), e, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list(tl), zz), Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.Lex{Lex.Str{}, ch <> bf, tk}, Equal.trans(Lex.Lex, Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.step.str.go(ch, bf, tk, U32.is_lt(Char.to_u32(ch), 32)), Lex.Lex{Lex.Str{}, ch <> bf, tk},
            Equal.cong(Lex.Class, Lex.Lex, zz => Lex.step(Lex.Str{}, zz, ch, bf, tk), Lex.classify(ch), Lex.CSpace{},
            ecls), Equal.cong(Bool, Lex.Lex, zz => Lex.step.str.go(ch, bf, tk, zz), U32.is_lt(Char.to_u32(ch), 32),
            False{}, ect)))), ({==}, hp)))))
    case Lex.COther{}:
      match ctl:
        case True{}:
          Unit{}
        case False{}:
          (M2.short_tail(ch, tl, h_s), ({==}, (Lex.Lex{Lex.Str{}, ch <> bf, tk}, (Equal.trans(Lex.Lex,
            Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.step(Lex.Str{}, Lex.classify(ch), ch,
            bf, tk)), Lex.run(String.to_list(tl), Lex.Lex{Lex.Str{}, ch <> bf, tk}), e, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list(tl), zz), Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.Lex{Lex.Str{}, ch <> bf, tk}, Equal.trans(Lex.Lex, Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.step.str.go(ch, bf, tk, U32.is_lt(Char.to_u32(ch), 32)), Lex.Lex{Lex.Str{}, ch <> bf, tk},
            Equal.cong(Lex.Class, Lex.Lex, zz => Lex.step(Lex.Str{}, zz, ch, bf, tk), Lex.classify(ch), Lex.COther{},
            ecls), Equal.cong(Bool, Lex.Lex, zz => Lex.step.str.go(ch, bf, tk, zz), U32.is_lt(Char.to_u32(ch), 32),
            False{}, ect)))), ({==}, hp)))))

# ss_quote
law ss_quote:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +stack: List<&2, Pull.Frame>
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for +e: M6.lx_e(tt, SCon{ch, tl}, Lex.Lex{Lex.Str{}, bf, tk})
  for +hp: {M6.prel(stack, False{}, M6.pst(Lex.Lex{Lex.Str{}, bf, tk})) == True{} : Bool}
  for cls: Lex.Class
  for +ecls: {Lex.classify(ch) == cls : Lex.Class}
  for ctl: Bool
  for +ect: {U32.is_lt(Char.to_u32(ch), 32) == ctl : Bool}
  M4.sinv(tt, tl, Pull.quote.go(Pull.span.kind(cls, ctl), ch, tl, stack, Pull.GNext{}, False{}))

def ss_quote(tt, ch, tl, stack, bf, tk, h_s, e, hp, cls, ecls, ctl, ect):
  match cls:
    case Lex.CQuote{}:
      match ctl:
        case True{}:
          M4.pp_split(M4.sinv(tt, tl, Pull.quote.go(Pull.span.kind(Lex.CQuote{}, True{}), ch, tl, stack, Pull.GNext{},
            False{})), M6.pst(Lex.Lex{Lex.Str{}, bf, tk}), stack, hp, +root => +qs => hp2 => epp => land_here(tt, tl,
            M4.lxi(Lex.TStr{Lex.text(bf)} <> tk), Lex.text(bf), stack, Pull.PSpan{"", 0}, qs, root, M2.short_tail(ch,
                tl,
            h_s), Equal.trans(Lex.Lex, Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl),
            Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk)), Lex.run(String.to_list(tl),
            M4.lxi(Lex.TStr{Lex.text(bf)} <> tk)), e, Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list(tl),
                zz),
            Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk), M4.lxi(Lex.TStr{Lex.text(bf)} <> tk),
                Equal.cong(Lex.Class,
            Lex.Lex, zz => Lex.step(Lex.Str{}, zz, ch, bf, tk), Lex.classify(ch), Lex.CQuote{}, ecls))), {==}, hp2,
            Equal.trans(Parse.P, M6.pst(M4.lxi(Lex.TStr{Lex.text(bf)} <> tk)), Parse.step(Lex.TStr{Lex.text(bf)},
            M6.pst(Lex.Lex{Lex.Str{}, bf, tk})), Parse.step(Lex.TStr{Lex.text(bf)}, Parse.P{False{}, root, qs}),
            M4.pst_push(Lex.TStr{Lex.text(bf)}, tk), Equal.cong(Parse.P, Parse.P,
                zz => Parse.step(Lex.TStr{Lex.text(bf)},
            zz), M6.pst(Lex.Lex{Lex.Str{}, bf, tk}), Parse.P{False{}, root, qs}, epp))))
        case False{}:
          M4.pp_split(M4.sinv(tt, tl, Pull.quote.go(Pull.span.kind(Lex.CQuote{}, False{}), ch, tl, stack, Pull.GNext{},
            False{})), M6.pst(Lex.Lex{Lex.Str{}, bf, tk}), stack, hp, +root => +qs => hp2 => epp => land_here(tt, tl,
            M4.lxi(Lex.TStr{Lex.text(bf)} <> tk), Lex.text(bf), stack, Pull.PSpan{"", 0}, qs, root, M2.short_tail(ch,
                tl,
            h_s), Equal.trans(Lex.Lex, Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl),
            Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk)), Lex.run(String.to_list(tl),
            M4.lxi(Lex.TStr{Lex.text(bf)} <> tk)), e, Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list(tl),
                zz),
            Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk), M4.lxi(Lex.TStr{Lex.text(bf)} <> tk),
                Equal.cong(Lex.Class,
            Lex.Lex, zz => Lex.step(Lex.Str{}, zz, ch, bf, tk), Lex.classify(ch), Lex.CQuote{}, ecls))), {==}, hp2,
            Equal.trans(Parse.P, M6.pst(M4.lxi(Lex.TStr{Lex.text(bf)} <> tk)), Parse.step(Lex.TStr{Lex.text(bf)},
            M6.pst(Lex.Lex{Lex.Str{}, bf, tk})), Parse.step(Lex.TStr{Lex.text(bf)}, Parse.P{False{}, root, qs}),
            M4.pst_push(Lex.TStr{Lex.text(bf)}, tk), Equal.cong(Parse.P, Parse.P,
                zz => Parse.step(Lex.TStr{Lex.text(bf)},
            zz), M6.pst(Lex.Lex{Lex.Str{}, bf, tk}), Parse.P{False{}, root, qs}, epp))))
    case Lex.CBack{}:
      match ctl:
        case True{}:
          Unit{}
        case False{}:
          (M2.short_tail(ch, tl, h_s), ({==}, (Lex.Lex{Lex.Esc{}, bf, tk}, (Equal.trans(Lex.Lex,
            Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.step(Lex.Str{}, Lex.classify(ch), ch,
            bf, tk)), Lex.run(String.to_list(tl), Lex.Lex{Lex.Esc{}, bf, tk}), e, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list(tl), zz), Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.Lex{Lex.Esc{}, bf, tk}, Equal.cong(Lex.Class, Lex.Lex, zz => Lex.step(Lex.Str{}, zz, ch, bf, tk),
            Lex.classify(ch), Lex.CBack{}, ecls))), ({==}, hp)))))
    case Lex.CPunct{+pt}:
      match ctl:
        case True{}:
          Unit{}
        case False{}:
          (M2.short_tail(ch, tl, h_s), ({==}, (Lex.Lex{Lex.Str{}, ch <> bf, tk}, (Equal.trans(Lex.Lex,
            Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.step(Lex.Str{}, Lex.classify(ch), ch,
            bf, tk)), Lex.run(String.to_list(tl), Lex.Lex{Lex.Str{}, ch <> bf, tk}), e, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list(tl), zz), Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.Lex{Lex.Str{}, ch <> bf, tk}, Equal.trans(Lex.Lex, Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.step.str.go(ch, bf, tk, U32.is_lt(Char.to_u32(ch), 32)), Lex.Lex{Lex.Str{}, ch <> bf, tk},
            Equal.cong(Lex.Class, Lex.Lex, zz => Lex.step(Lex.Str{}, zz, ch, bf, tk), Lex.classify(ch), Lex.CPunct{pt},
            ecls), Equal.cong(Bool, Lex.Lex, zz => Lex.step.str.go(ch, bf, tk, zz), U32.is_lt(Char.to_u32(ch), 32),
            False{}, ect)))), ({==}, hp)))))
    case Lex.CSpace{}:
      match ctl:
        case True{}:
          Unit{}
        case False{}:
          (M2.short_tail(ch, tl, h_s), ({==}, (Lex.Lex{Lex.Str{}, ch <> bf, tk}, (Equal.trans(Lex.Lex,
            Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.step(Lex.Str{}, Lex.classify(ch), ch,
            bf, tk)), Lex.run(String.to_list(tl), Lex.Lex{Lex.Str{}, ch <> bf, tk}), e, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list(tl), zz), Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.Lex{Lex.Str{}, ch <> bf, tk}, Equal.trans(Lex.Lex, Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.step.str.go(ch, bf, tk, U32.is_lt(Char.to_u32(ch), 32)), Lex.Lex{Lex.Str{}, ch <> bf, tk},
            Equal.cong(Lex.Class, Lex.Lex, zz => Lex.step(Lex.Str{}, zz, ch, bf, tk), Lex.classify(ch), Lex.CSpace{},
            ecls), Equal.cong(Bool, Lex.Lex, zz => Lex.step.str.go(ch, bf, tk, zz), U32.is_lt(Char.to_u32(ch), 32),
            False{}, ect)))), ({==}, hp)))))
    case Lex.COther{}:
      match ctl:
        case True{}:
          Unit{}
        case False{}:
          (M2.short_tail(ch, tl, h_s), ({==}, (Lex.Lex{Lex.Str{}, ch <> bf, tk}, (Equal.trans(Lex.Lex,
            Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.step(Lex.Str{}, Lex.classify(ch), ch,
            bf, tk)), Lex.run(String.to_list(tl), Lex.Lex{Lex.Str{}, ch <> bf, tk}), e, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list(tl), zz), Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.Lex{Lex.Str{}, ch <> bf, tk}, Equal.trans(Lex.Lex, Lex.step(Lex.Str{}, Lex.classify(ch), ch, bf, tk),
            Lex.step.str.go(ch, bf, tk, U32.is_lt(Char.to_u32(ch), 32)), Lex.Lex{Lex.Str{}, ch <> bf, tk},
            Equal.cong(Lex.Class, Lex.Lex, zz => Lex.step(Lex.Str{}, zz, ch, bf, tk), Lex.classify(ch), Lex.COther{},
            ecls), Equal.cong(Bool, Lex.Lex, zz => Lex.step.str.go(ch, bf, tk, zz), U32.is_lt(Char.to_u32(ch), 32),
            False{}, ect)))), ({==}, hp)))))

# the character after a backslash, once its escape's character is named
law ss_escp:
  for +tt: String
  for +tl: String
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +h_s: {D1.short(tl) == True{} : Bool}
  for um: Maybe<&2, Char>
  for +e: M6.lx_e(tt, tl, Lex.escape.put(um, bf, tk))
  for +hp: {M6.prel(stack, False{}, M6.pst(Lex.Lex{Lex.Esc{}, bf, tk})) == True{} : Bool}
  M4.sinv(tt, tl, Pull.esc.put(tl, buf, stack, Pull.GNext{}, False{}, um))

def ss_escp(_tt, _tl, _buf, _stack, bf, tk, h_s, um, e, hp):
  match um:
    case Some{+cc}:
      (h_s, ({==}, (Lex.Lex{Lex.Str{}, cc <> bf, tk}, (e, ({==}, hp)))))
    case None{}:
      Unit{}

# the character after a backslash, once whether it is u is named
law ss_esc:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for +e: M6.lx_e(tt, SCon{ch, tl}, Lex.Lex{Lex.Esc{}, bf, tk})
  for +hp: {M6.prel(stack, False{}, M6.pst(Lex.Lex{Lex.Esc{}, bf, tk})) == True{} : Bool}
  for isu: Bool
  for +eu: {U32.is_eq(Char.to_u32(ch), 117) == isu : Bool}
  M4.sinv(tt, tl, Pull.esc.hit.go(ch, tl, buf, stack, Pull.GNext{}, False{}, isu))

def ss_esc(tt, ch, tl, buf, stack, bf, tk, h_s, e, hp, isu, eu):
  match isu:
    case True{}:
      (M2.short_tail(ch, tl, h_s), ({==}, (Lex.Lex{Lex.Uni{3n, 0}, bf, tk}, (Equal.trans(Lex.Lex,
        Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.escape.go(ch, bf, tk,
        U32.is_eq(Char.to_u32(ch), 117))), Lex.run(String.to_list(tl), Lex.Lex{Lex.Uni{3n, 0}, bf, tk}), e,
        Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list(tl), zz), Lex.escape.go(ch, bf, tk,
        U32.is_eq(Char.to_u32(ch), 117)), Lex.Lex{Lex.Uni{3n, 0}, bf, tk}, Equal.cong(Bool, Lex.Lex,
        zz => Lex.escape.go(ch, bf, tk, zz), U32.is_eq(Char.to_u32(ch), 117), True{}, eu))), ({==}, hp)))))
    case False{}:
      ss_escp(tt, tl, buf, stack, bf, tk, M2.short_tail(ch, tl, h_s), Lex.unescape(ch), Equal.trans(Lex.Lex,
        Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.escape.go(ch, bf, tk,
        U32.is_eq(Char.to_u32(ch), 117))), Lex.run(String.to_list(tl), Lex.escape.put(Lex.unescape(ch), bf, tk)), e,
        Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list(tl), zz), Lex.escape.go(ch, bf, tk,
        U32.is_eq(Char.to_u32(ch), 117)), Lex.escape.put(Lex.unescape(ch), bf, tk), Equal.cong(Bool, Lex.Lex,
        zz => Lex.escape.go(ch, bf, tk, zz), U32.is_eq(Char.to_u32(ch), 117), False{}, eu))), hp)

# four hex digits of a \u escape are in, once the kind of code point is named
law ss_uend:
  for +tt: String
  for +tl: String
  for +cp: U32
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +h_s: {D1.short(tl) == True{} : Bool}
  for sr: Lex.Sur
  for +e: M6.lx_e(tt, tl, Lex.unicode.end.go(cp, bf, tk, sr))
  for +hp: {M6.prel(stack, False{}, M6.pst(Lex.Lex{Lex.Esc{}, bf, tk})) == True{} : Bool}
  M4.sinv(tt, tl, Pull.uni.end.go(tl, cp, buf, stack, Pull.GNext{}, False{}, sr))

def ss_uend(_tt, _tl, cp, _buf, _stack, bf, tk, h_s, sr, e, hp):
  match sr:
    case Lex.SOk{}:
      (h_s, ({==}, (Lex.Lex{Lex.Str{}, Char.from_u32(cp) <> bf, tk}, (e, ({==}, hp)))))
    case Lex.SHi{}:
      (h_s, ({==}, (Lex.Lex{Lex.Hi{cp}, bf, tk}, (e, ({==}, hp)))))
    case Lex.SLo{}:
      Unit{}

# one hex digit of a \u escape is in
law ss_uput:
  for +tt: String
  for +tl: String
  for left: Nat
  for +acc: U32
  for +dig: U32
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +h_s: {D1.short(tl) == True{} : Bool}
  for +e: M6.lx_e(tt, tl, Lex.unicode.put(left, acc, dig, bf, tk))
  for +hp: {M6.prel(stack, False{}, M6.pst(Lex.Lex{Lex.Esc{}, bf, tk})) == True{} : Bool}
  M4.sinv(tt, tl, Pull.uni.put(tl, left, acc, dig, buf, stack, Pull.GNext{}, False{}))

def ss_uput(tt, tl, left, acc, dig, buf, stack, bf, tk, h_s, e, hp):
  match left:
    case 0n:
      ss_uend(tt, tl, (acc * 16 + dig : U32), buf, stack, bf, tk, h_s, Lex.unicode.sur((acc * 16 + dig : U32)), e, hp)
    case 1n+pp:
      (h_s, ({==}, (Lex.Lex{Lex.Uni{pp, (acc * 16 + dig : U32)}, bf, tk}, (e, ({==}, hp)))))

# a hex digit of a \u escape, once whether it is one is named
law ss_uni:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +left: Nat
  for +acc: U32
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for +e: M6.lx_e(tt, SCon{ch, tl}, Lex.Lex{Lex.Uni{left, acc}, bf, tk})
  for +hp: {M6.prel(stack, False{}, M6.pst(Lex.Lex{Lex.Uni{left, acc}, bf, tk})) == True{} : Bool}
  for hx: Bool
  for +ehx: {Lex.hex.ok(Char.to_u32(ch)) == hx : Bool}
  M4.sinv(tt, tl, Pull.uni.hit.go(ch, tl, left, acc, buf, stack, Pull.GNext{}, False{}, hx))

def ss_uni(tt, ch, tl, left, acc, buf, stack, bf, tk, h_s, e, hp, hx, ehx):
  match hx:
    case False{}:
      Unit{}
    case True{}:
      ss_uput(tt, tl, left, acc, Lex.hex(ch), buf, stack, bf, tk, M2.short_tail(ch, tl, h_s), Equal.trans(Lex.Lex,
        Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.unicode.go(left, acc, ch, bf, tk,
        Lex.hex.ok(Char.to_u32(ch)))), Lex.run(String.to_list(tl), Lex.unicode.put(left, acc, Lex.hex(ch), bf, tk)), e,
        Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list(tl), zz), Lex.unicode.go(left, acc, ch, bf, tk,
        Lex.hex.ok(Char.to_u32(ch))), Lex.unicode.put(left, acc, Lex.hex(ch), bf, tk), Equal.cong(Bool, Lex.Lex,
        zz => Lex.unicode.go(left, acc, ch, bf, tk, zz), Lex.hex.ok(Char.to_u32(ch)), True{}, ehx))),
        hp)

# the character after a high surrogate's escape, by its class
law ss_hi:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +hi: U32
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for +e: M6.lx_e(tt, SCon{ch, tl}, Lex.Lex{Lex.Hi{hi}, bf, tk})
  for +hp: {M6.prel(stack, False{}, M6.pst(Lex.Lex{Lex.Hi{hi}, bf, tk})) == True{} : Bool}
  for cls: Lex.Class
  for +ecls: {Lex.classify(ch) == cls : Lex.Class}
  M4.sinv(tt, tl, Pull.hi.hit.go(tl, hi, buf, stack, Pull.GNext{}, False{}, cls))

def ss_hi(tt, ch, tl, hi, _buf, _stack, bf, tk, h_s, e, hp, cls, ecls):
  match cls:
    case Lex.CBack{}:
      (M2.short_tail(ch, tl, h_s), ({==}, (Lex.Lex{Lex.HiEsc{hi}, bf, tk}, (Equal.trans(Lex.Lex,
        Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.step.hi.go(hi, bf, tk,
        U32.is_eq(Char.to_u32(ch), 92))), Lex.run(String.to_list(tl), Lex.Lex{Lex.HiEsc{hi}, bf, tk}), e,
        Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list(tl), zz), Lex.step.hi.go(hi, bf, tk,
        U32.is_eq(Char.to_u32(ch), 92)), Lex.Lex{Lex.HiEsc{hi}, bf, tk}, Equal.cong(U32, Lex.Lex,
        zz => Lex.step.hi.go(hi, bf, tk, U32.is_eq(zz, 92)), Char.to_u32(ch), 92, M2.cls_back(ch, ecls)))), ({==},
            hp)))))
    case Lex.CPunct{_}:
      Unit{}
    case Lex.CQuote{}:
      Unit{}
    case Lex.CSpace{}:
      Unit{}
    case Lex.COther{}:
      Unit{}

# the character after a high surrogate's escape and a backslash, once whether it is u is named
law ss_hiesc:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +hi: U32
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for +e: M6.lx_e(tt, SCon{ch, tl}, Lex.Lex{Lex.HiEsc{hi}, bf, tk})
  for +hp: {M6.prel(stack, False{}, M6.pst(Lex.Lex{Lex.HiEsc{hi}, bf, tk})) == True{} : Bool}
  for isu: Bool
  for +eu: {U32.is_eq(Char.to_u32(ch), 117) == isu : Bool}
  M4.sinv(tt, tl, Pull.hiesc.hit.go(tl, hi, buf, stack, Pull.GNext{}, False{}, isu))

def ss_hiesc(tt, ch, tl, hi, _buf, _stack, bf, tk, h_s, e, hp, isu, eu):
  match isu:
    case True{}:
      (M2.short_tail(ch, tl, h_s), ({==}, (Lex.Lex{Lex.Lo{3n, 0, hi}, bf, tk}, (Equal.trans(Lex.Lex,
        Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.step.hiesc.go(hi, bf, tk,
        U32.is_eq(Char.to_u32(ch), 117))), Lex.run(String.to_list(tl), Lex.Lex{Lex.Lo{3n, 0, hi}, bf, tk}), e,
        Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list(tl), zz), Lex.step.hiesc.go(hi, bf, tk,
        U32.is_eq(Char.to_u32(ch), 117)), Lex.Lex{Lex.Lo{3n, 0, hi}, bf, tk}, Equal.cong(Bool, Lex.Lex,
        zz => Lex.step.hiesc.go(hi, bf, tk, zz), U32.is_eq(Char.to_u32(ch), 117), True{}, eu))), ({==}, hp)))))
    case False{}:
      Unit{}

# four hex digits of a low surrogate's \u escape are in, once its kind is named
law ss_lend:
  for +tt: String
  for +tl: String
  for +lo: U32
  for +hi: U32
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +h_s: {D1.short(tl) == True{} : Bool}
  for sr: Lex.Sur
  for +e: M6.lx_e(tt, tl, Lex.unicode.low.end.go(lo, hi, bf, tk, sr))
  for +hp: {M6.prel(stack, False{}, M6.pst(Lex.Lex{Lex.Esc{}, bf, tk})) == True{} : Bool}
  M4.sinv(tt, tl, Pull.lo.end.go(tl, lo, hi, buf, stack, Pull.GNext{}, False{}, sr))

def ss_lend(_tt, _tl, lo, hi, _buf, _stack, bf, tk, h_s, sr, e, hp):
  match sr:
    case Lex.SLo{}:
      (h_s, ({==}, (Lex.Lex{Lex.Str{}, Char.from_u32(Lex.unicode.pair(hi, lo)) <> bf, tk}, (e, ({==}, hp)))))
    case Lex.SOk{}:
      Unit{}
    case Lex.SHi{}:
      Unit{}

# one hex digit of a low surrogate's \u escape is in
law ss_lput:
  for +tt: String
  for +tl: String
  for left: Nat
  for +acc: U32
  for +hi: U32
  for +dig: U32
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +h_s: {D1.short(tl) == True{} : Bool}
  for +e: M6.lx_e(tt, tl, Lex.unicode.low.put(left, acc, hi, dig, bf, tk))
  for +hp: {M6.prel(stack, False{}, M6.pst(Lex.Lex{Lex.Esc{}, bf, tk})) == True{} : Bool}
  M4.sinv(tt, tl, Pull.lo.put(tl, left, acc, hi, dig, buf, stack, Pull.GNext{}, False{}))

def ss_lput(tt, tl, left, acc, hi, dig, buf, stack, bf, tk, h_s, e, hp):
  match left:
    case 0n:
      ss_lend(tt, tl, (acc * 16 + dig : U32), hi, buf, stack, bf, tk, h_s, Lex.unicode.sur((acc * 16 + dig : U32)), e,
        hp)
    case 1n+pp:
      (h_s, ({==}, (Lex.Lex{Lex.Lo{pp, (acc * 16 + dig : U32), hi}, bf, tk}, (e, ({==}, hp)))))

# a hex digit of a low surrogate's \u escape, once whether it is one is named
law ss_lo:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +left: Nat
  for +acc: U32
  for +hi: U32
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for +e: M6.lx_e(tt, SCon{ch, tl}, Lex.Lex{Lex.Lo{left, acc, hi}, bf, tk})
  for +hp: {M6.prel(stack, False{}, M6.pst(Lex.Lex{Lex.Lo{left, acc, hi}, bf, tk})) == True{} : Bool}
  for hx: Bool
  for +ehx: {Lex.hex.ok(Char.to_u32(ch)) == hx : Bool}
  M4.sinv(tt, tl, Pull.lo.hit.go(ch, tl, left, acc, hi, buf, stack, Pull.GNext{}, False{}, hx))

def ss_lo(tt, ch, tl, left, acc, hi, buf, stack, bf, tk, h_s, e, hp, hx, ehx):
  match hx:
    case False{}:
      Unit{}
    case True{}:
      ss_lput(tt, tl, left, acc, hi, Lex.hex(ch), buf, stack, bf, tk, M2.short_tail(ch, tl, h_s), Equal.trans(Lex.Lex,
        Lex.run(String.to_list(tt), M6.lx0()), Lex.run(String.to_list(tl), Lex.unicode.low.go(left, acc, hi, ch, bf, tk,
        Lex.hex.ok(Char.to_u32(ch)))), Lex.run(String.to_list(tl), Lex.unicode.low.put(left, acc, hi, Lex.hex(ch), bf,
        tk)), e, Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list(tl), zz), Lex.unicode.low.go(left, acc, hi,
        ch, bf, tk, Lex.hex.ok(Char.to_u32(ch))), Lex.unicode.low.put(left, acc, hi, Lex.hex(ch), bf, tk),
        Equal.cong(Bool, Lex.Lex, zz => Lex.unicode.low.go(left, acc, hi, ch, bf, tk, zz), Lex.hex.ok(Char.to_u32(ch)),
        True{}, ehx))),
        hp)

# laws/CursorEventsMatchParse.bend: the cursor walks in step with the lexer and the parser

# one character in a string mode, once the lexer's state is in hand
law sm_copy.l:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for done: Bool
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for hd: {done == False{} : Bool}
  for +lx: Lex.Lex
  for +e: M6.lx_e(tt, SCon{ch, tl}, lx)
  for +hm: {M4.lxmode(lx) == M4.mo(Pull.MCopy{buf}) : Lex.Mode}
  for +hp: {M6.prel(stack, False{}, M6.pst(lx)) == True{} : Bool}
  M4.sinv(tt, tl, Pull.copy.hit(ch, tl, buf, stack, Pull.GNext{}, done, False{}, Lex.classify(ch),
    U32.is_lt(Char.to_u32(ch), 32)))

def sm_copy.l(tt, ch, tl, buf, stack, done, h_s, hd, lx, e, hm, hp):
  match lx:
    case Lex.Lex{+md, +bf, +tk}:
      es = Equal.sym(Bool, done, False{}, hd)
      %es : M4.sinv(tt, tl, Pull.copy.hit(ch, tl, buf, stack, Pull.GNext{}, _, False{}, Lex.classify(ch),
        U32.is_lt(Char.to_u32(ch), 32)))
      ss_copy(tt, ch, tl, buf, stack, bf, tk, h_s, lxfix_e(tt, SCon{ch, tl}, md, Lex.Str{}, bf, tk, hm, e),
        lxfix_p(stack, md, Lex.Str{}, bf, tk, hm, hp), Lex.classify(ch), {==}, U32.is_lt(Char.to_u32(ch), 32), {==})

# one character in a string mode: the cursor fails or stays in step
law sm_copy:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for hh: M4.sminv(tt, SCon{ch, tl}, Pull.MCopy{buf}, stack, done)
  M4.sinv(tt, tl, Pull.copy.hit(ch, tl, buf, stack, Pull.GNext{}, done, False{}, Lex.classify(ch),
    U32.is_lt(Char.to_u32(ch), 32)))

def sm_copy(tt, ch, tl, buf, stack, done, hh):
  (h_s, (hd, (+lx, (e, (hm, hp))))) = hh
  sm_copy.l(tt, ch, tl, buf, stack, done, h_s, hd, lx, e, hm, hp)

# one character in a string mode, once the lexer's state is in hand
law sm_quote.l:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +stack: List<&2, Pull.Frame>
  for done: Bool
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for hd: {done == False{} : Bool}
  for +lx: Lex.Lex
  for +e: M6.lx_e(tt, SCon{ch, tl}, lx)
  for +hm: {M4.lxmode(lx) == M4.mo(Pull.MQuote{}) : Lex.Mode}
  for +hp: {M6.prel(stack, False{}, M6.pst(lx)) == True{} : Bool}
  M4.sinv(tt, tl, Pull.quote.first(ch, tl, stack, Pull.GNext{}, done))

def sm_quote.l(tt, ch, tl, stack, done, h_s, hd, lx, e, hm, hp):
  match lx:
    case Lex.Lex{+md, +bf, +tk}:
      es = Equal.sym(Bool, done, False{}, hd)
      %es : M4.sinv(tt, tl, Pull.quote.first(ch, tl, stack, Pull.GNext{}, _))
      ss_quote(tt, ch, tl, stack, bf, tk, h_s, lxfix_e(tt, SCon{ch, tl}, md, Lex.Str{}, bf, tk, hm, e), lxfix_p(stack,
        md, Lex.Str{}, bf, tk, hm, hp), Lex.classify(ch), {==}, U32.is_lt(Char.to_u32(ch), 32), {==})

# one character in a string mode: the cursor fails or stays in step
law sm_quote:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for hh: M4.sminv(tt, SCon{ch, tl}, Pull.MQuote{}, stack, done)
  M4.sinv(tt, tl, Pull.quote.first(ch, tl, stack, Pull.GNext{}, done))

def sm_quote(tt, ch, tl, stack, done, hh):
  (h_s, (hd, (+lx, (e, (hm, hp))))) = hh
  sm_quote.l(tt, ch, tl, stack, done, h_s, hd, lx, e, hm, hp)

# one character in a string mode, once the lexer's state is in hand
law sm_span.l:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +cut: String
  for +nn: U32
  for +stack: List<&2, Pull.Frame>
  for done: Bool
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for hd: {done == False{} : Bool}
  for +lx: Lex.Lex
  for +e: M6.lx_e(tt, SCon{ch, tl}, lx)
  for +hm: {M4.lxmode(lx) == M4.mo(Pull.MSpan{cut, nn}) : Lex.Mode}
  for +hp: {M6.prel(stack, False{}, M6.pst(lx)) == True{} : Bool}
  M4.sinv(tt, tl, Pull.span.advance(Pull.span.kind.of(ch), cut, nn, stack, Pull.GNext{}, done))

def sm_span.l(tt, ch, tl, cut, nn, stack, done, h_s, hd, lx, e, hm, hp):
  match lx:
    case Lex.Lex{+md, +bf, +tk}:
      es = Equal.sym(Bool, done, False{}, hd)
      %es : M4.sinv(tt, tl, Pull.span.advance(Pull.span.kind.of(ch), cut, nn, stack, Pull.GNext{}, _))
      ss_span(tt, ch, tl, cut, nn, stack, bf, tk, h_s, lxfix_e(tt, SCon{ch, tl}, md, Lex.Str{}, bf, tk, hm, e),
        lxfix_p(stack, md, Lex.Str{}, bf, tk, hm, hp), Lex.classify(ch), {==}, U32.is_lt(Char.to_u32(ch), 32), {==})

# one character in a string mode: the cursor fails or stays in step
law sm_span:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +cut: String
  for +nn: U32
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for hh: M4.sminv(tt, SCon{ch, tl}, Pull.MSpan{cut, nn}, stack, done)
  M4.sinv(tt, tl, Pull.span.advance(Pull.span.kind.of(ch), cut, nn, stack, Pull.GNext{}, done))

def sm_span(tt, ch, tl, cut, nn, stack, done, hh):
  (h_s, (hd, (+lx, (e, (hm, hp))))) = hh
  sm_span.l(tt, ch, tl, cut, nn, stack, done, h_s, hd, lx, e, hm, hp)

# one character in a string mode, once the lexer's state is in hand
law sm_esc.l:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for done: Bool
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for hd: {done == False{} : Bool}
  for +lx: Lex.Lex
  for +e: M6.lx_e(tt, SCon{ch, tl}, lx)
  for +hm: {M4.lxmode(lx) == M4.mo(Pull.MEsc{buf}) : Lex.Mode}
  for +hp: {M6.prel(stack, False{}, M6.pst(lx)) == True{} : Bool}
  M4.sinv(tt, tl, Pull.esc.hit(ch, tl, buf, stack, Pull.GNext{}, done, False{}))

def sm_esc.l(tt, ch, tl, buf, stack, done, h_s, hd, lx, e, hm, hp):
  match lx:
    case Lex.Lex{+md, +bf, +tk}:
      es = Equal.sym(Bool, done, False{}, hd)
      %es : M4.sinv(tt, tl, Pull.esc.hit(ch, tl, buf, stack, Pull.GNext{}, _, False{}))
      ss_esc(tt, ch, tl, buf, stack, bf, tk, h_s, lxfix_e(tt, SCon{ch, tl}, md, Lex.Esc{}, bf, tk, hm, e),
        lxfix_p(stack, md, Lex.Esc{}, bf, tk, hm, hp), U32.is_eq(Char.to_u32(ch), 117), {==})

# one character in a string mode: the cursor fails or stays in step
law sm_esc:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for hh: M4.sminv(tt, SCon{ch, tl}, Pull.MEsc{buf}, stack, done)
  M4.sinv(tt, tl, Pull.esc.hit(ch, tl, buf, stack, Pull.GNext{}, done, False{}))

def sm_esc(tt, ch, tl, buf, stack, done, hh):
  (h_s, (hd, (+lx, (e, (hm, hp))))) = hh
  sm_esc.l(tt, ch, tl, buf, stack, done, h_s, hd, lx, e, hm, hp)

# one character in a string mode, once the lexer's state is in hand
law sm_uni.l:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +left: Nat
  for +acc: U32
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for done: Bool
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for hd: {done == False{} : Bool}
  for +lx: Lex.Lex
  for +e: M6.lx_e(tt, SCon{ch, tl}, lx)
  for +hm: {M4.lxmode(lx) == M4.mo(Pull.MUni{left, acc, buf}) : Lex.Mode}
  for +hp: {M6.prel(stack, False{}, M6.pst(lx)) == True{} : Bool}
  M4.sinv(tt, tl, Pull.uni.hit(ch, tl, left, acc, buf, stack, Pull.GNext{}, done, False{}))

def sm_uni.l(tt, ch, tl, left, acc, buf, stack, done, h_s, hd, lx, e, hm, hp):
  match lx:
    case Lex.Lex{+md, +bf, +tk}:
      es = Equal.sym(Bool, done, False{}, hd)
      %es : M4.sinv(tt, tl, Pull.uni.hit(ch, tl, left, acc, buf, stack, Pull.GNext{}, _, False{}))
      ss_uni(tt, ch, tl, left, acc, buf, stack, bf, tk, h_s, lxfix_e(tt, SCon{ch, tl}, md, Lex.Uni{left, acc}, bf, tk,
        hm, e), lxfix_p(stack, md, Lex.Uni{left, acc}, bf, tk, hm, hp), Lex.hex.ok(Char.to_u32(ch)), {==})

# one character in a string mode: the cursor fails or stays in step
law sm_uni:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +left: Nat
  for +acc: U32
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for hh: M4.sminv(tt, SCon{ch, tl}, Pull.MUni{left, acc, buf}, stack, done)
  M4.sinv(tt, tl, Pull.uni.hit(ch, tl, left, acc, buf, stack, Pull.GNext{}, done, False{}))

def sm_uni(tt, ch, tl, left, acc, buf, stack, done, hh):
  (h_s, (hd, (+lx, (e, (hm, hp))))) = hh
  sm_uni.l(tt, ch, tl, left, acc, buf, stack, done, h_s, hd, lx, e, hm, hp)

# one character in a string mode, once the lexer's state is in hand
law sm_hi.l:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +hi: U32
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for done: Bool
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for hd: {done == False{} : Bool}
  for +lx: Lex.Lex
  for +e: M6.lx_e(tt, SCon{ch, tl}, lx)
  for +hm: {M4.lxmode(lx) == M4.mo(Pull.MHi{hi, buf}) : Lex.Mode}
  for +hp: {M6.prel(stack, False{}, M6.pst(lx)) == True{} : Bool}
  M4.sinv(tt, tl, Pull.hi.hit(tl, hi, buf, stack, Pull.GNext{}, done, False{}, Lex.classify(ch)))

def sm_hi.l(tt, ch, tl, hi, buf, stack, done, h_s, hd, lx, e, hm, hp):
  match lx:
    case Lex.Lex{+md, +bf, +tk}:
      es = Equal.sym(Bool, done, False{}, hd)
      %es : M4.sinv(tt, tl, Pull.hi.hit(tl, hi, buf, stack, Pull.GNext{}, _, False{}, Lex.classify(ch)))
      ss_hi(tt, ch, tl, hi, buf, stack, bf, tk, h_s, lxfix_e(tt, SCon{ch, tl}, md, Lex.Hi{hi}, bf, tk, hm, e),
        lxfix_p(stack, md, Lex.Hi{hi}, bf, tk, hm, hp), Lex.classify(ch), {==})

# one character in a string mode: the cursor fails or stays in step
law sm_hi:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +hi: U32
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for hh: M4.sminv(tt, SCon{ch, tl}, Pull.MHi{hi, buf}, stack, done)
  M4.sinv(tt, tl, Pull.hi.hit(tl, hi, buf, stack, Pull.GNext{}, done, False{}, Lex.classify(ch)))

def sm_hi(tt, ch, tl, hi, buf, stack, done, hh):
  (h_s, (hd, (+lx, (e, (hm, hp))))) = hh
  sm_hi.l(tt, ch, tl, hi, buf, stack, done, h_s, hd, lx, e, hm, hp)

# one character in a string mode, once the lexer's state is in hand
law sm_hiesc.l:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +hi: U32
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for done: Bool
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for hd: {done == False{} : Bool}
  for +lx: Lex.Lex
  for +e: M6.lx_e(tt, SCon{ch, tl}, lx)
  for +hm: {M4.lxmode(lx) == M4.mo(Pull.MHiEsc{hi, buf}) : Lex.Mode}
  for +hp: {M6.prel(stack, False{}, M6.pst(lx)) == True{} : Bool}
  M4.sinv(tt, tl, Pull.hiesc.hit(ch, tl, hi, buf, stack, Pull.GNext{}, done, False{}))

def sm_hiesc.l(tt, ch, tl, hi, buf, stack, done, h_s, hd, lx, e, hm, hp):
  match lx:
    case Lex.Lex{+md, +bf, +tk}:
      es = Equal.sym(Bool, done, False{}, hd)
      %es : M4.sinv(tt, tl, Pull.hiesc.hit(ch, tl, hi, buf, stack, Pull.GNext{}, _, False{}))
      ss_hiesc(tt, ch, tl, hi, buf, stack, bf, tk, h_s, lxfix_e(tt, SCon{ch, tl}, md, Lex.HiEsc{hi}, bf, tk, hm, e),
        lxfix_p(stack, md, Lex.HiEsc{hi}, bf, tk, hm, hp), U32.is_eq(Char.to_u32(ch), 117), {==})

# one character in a string mode: the cursor fails or stays in step
law sm_hiesc:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +hi: U32
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for hh: M4.sminv(tt, SCon{ch, tl}, Pull.MHiEsc{hi, buf}, stack, done)
  M4.sinv(tt, tl, Pull.hiesc.hit(ch, tl, hi, buf, stack, Pull.GNext{}, done, False{}))

def sm_hiesc(tt, ch, tl, hi, buf, stack, done, hh):
  (h_s, (hd, (+lx, (e, (hm, hp))))) = hh
  sm_hiesc.l(tt, ch, tl, hi, buf, stack, done, h_s, hd, lx, e, hm, hp)

# one character in a string mode, once the lexer's state is in hand
law sm_lo.l:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +left: Nat
  for +acc: U32
  for +hi: U32
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for done: Bool
  for +h_s: {D1.short(SCon{ch, tl}) == True{} : Bool}
  for hd: {done == False{} : Bool}
  for +lx: Lex.Lex
  for +e: M6.lx_e(tt, SCon{ch, tl}, lx)
  for +hm: {M4.lxmode(lx) == M4.mo(Pull.MLo{left, acc, hi, buf}) : Lex.Mode}
  for +hp: {M6.prel(stack, False{}, M6.pst(lx)) == True{} : Bool}
  M4.sinv(tt, tl, Pull.lo.hit(ch, tl, left, acc, hi, buf, stack, Pull.GNext{}, done, False{}))

def sm_lo.l(tt, ch, tl, left, acc, hi, buf, stack, done, h_s, hd, lx, e, hm, hp):
  match lx:
    case Lex.Lex{+md, +bf, +tk}:
      es = Equal.sym(Bool, done, False{}, hd)
      %es : M4.sinv(tt, tl, Pull.lo.hit(ch, tl, left, acc, hi, buf, stack, Pull.GNext{}, _, False{}))
      ss_lo(tt, ch, tl, left, acc, hi, buf, stack, bf, tk, h_s, lxfix_e(tt, SCon{ch, tl}, md, Lex.Lo{left, acc, hi},
        bf, tk, hm, e), lxfix_p(stack, md, Lex.Lo{left, acc, hi}, bf, tk, hm, hp), Lex.hex.ok(Char.to_u32(ch)), {==})

# one character in a string mode: the cursor fails or stays in step
law sm_lo:
  for +tt: String
  for +ch: Char
  for +tl: String
  for +left: Nat
  for +acc: U32
  for +hi: U32
  for +buf: List<&2, Char>
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for hh: M4.sminv(tt, SCon{ch, tl}, Pull.MLo{left, acc, hi, buf}, stack, done)
  M4.sinv(tt, tl, Pull.lo.hit(ch, tl, left, acc, hi, buf, stack, Pull.GNext{}, done, False{}))

def sm_lo(tt, ch, tl, left, acc, hi, buf, stack, done, hh):
  (h_s, (hd, (+lx, (e, (hm, hp))))) = hh
  sm_lo.l(tt, ch, tl, left, acc, hi, buf, stack, done, h_s, hd, lx, e, hm, hp)

# a word the cursor reads, from its invariant: it lands in step or fails
law wm_go:
  for +tt: String
  for +xx: String
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for +stack: List<&2, Pull.Frame>
  for +done: Bool
  for hh: M4.wminv(tt, xx, buf, nn, num, stack, done)
  M4.sinv(tt, "", Pull.word.burst(xx, buf, nn, num, stack, Pull.GNext{}, False{}))

def wm_go(tt, xx, buf, nn, num, stack, _done, hh):
  (_hd, (hv, (hsx, (hn, (+cut, (e_d, (e_r, (h_c, (+tk, (e, hp)))))))))) = hh
  M4.wb(tt, xx, buf, nn, num, stack, tk, cut, hv, hsx, hn, e_d, e_r, h_c, e, hp)

# the end of the text between tokens: the end of a text that parses, or a failure
law eof_go:
  for +tt: String
  for +stack: List<&2, Pull.Frame>
  for done: Bool
  for +hst: {D1.short(tt) == True{} : Bool}
  for hh: M6.cinv(tt, Pull.Cur{"", stack, done, False{}})
  fok2(tt, Pull.idle.eof(stack, Pull.GNext{}, done, False{}))

def eof_go(tt, stack, done, hst, hh):
  match done:
    case True{}:
      (_h_s, (+lx, (e, (hc, hp)))) = hh
      fin_some(tt, lx, stack, hst, e, hc, hp)
    case False{}:
      Unit{}

# a walk from a step state in step: its result is in step
law pgo_inv:
  for +tt: String
  for +ff: Nat
  for +xx: String
  for +st: Pull.St
  for hh: M4.sinv(tt, xx, st)
  for +hst: {D1.short(tt) == True{} : Bool}
  oinv(tt, Pull.next.go(ff, xx, st))

def pgo_inv(tt, ff, xx, st, hh, hst):
  match ff xx st:
    case 0n SNil{} Pull.S{Pull.MDone{+s1, +v1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SNil{} Pull.S{Pull.MRest{+s1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SNil{} Pull.S{Pull.MIdle{}, +stack, +goal, +done, +bad}:
      hh
    case 0n SNil{} Pull.S{Pull.MWord{+b1, +n1, +m1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SNil{} Pull.S{Pull.MSpan{+c1, +n1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SNil{} Pull.S{Pull.MCopy{+b1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SNil{} Pull.S{Pull.MEsc{+b1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SNil{} Pull.S{Pull.MUni{+l1, +a1, +b1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SNil{} Pull.S{Pull.MHi{+h1, +b1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SNil{} Pull.S{Pull.MHiEsc{+h1, +b1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SNil{} Pull.S{Pull.MLo{+l1, +a1, +h1, +b1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SNil{} Pull.S{Pull.MSkStr{}, +stack, +goal, +done, +bad}:
      hh
    case 0n SNil{} Pull.S{Pull.MSkEsc{}, +stack, +goal, +done, +bad}:
      hh
    case 0n SNil{} Pull.S{Pull.MSkUni{+l1, +a1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SNil{} Pull.S{Pull.MSkHi{+h1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SNil{} Pull.S{Pull.MSkHiEsc{+h1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SNil{} Pull.S{Pull.MSkLo{+l1, +a1, +h1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SNil{} Pull.S{Pull.MQuote{}, +stack, +goal, +done, +bad}:
      hh
    case 0n SNil{} Pull.S{Pull.MJump{+r1, +j1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MDone{+s1, +v1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MRest{+s1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MIdle{}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MWord{+b1, +n1, +m1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSpan{+c1, +n1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MCopy{+b1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MEsc{+b1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MUni{+l1, +a1, +b1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MHi{+h1, +b1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MHiEsc{+h1, +b1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MLo{+l1, +a1, +h1, +b1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSkStr{}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSkEsc{}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSkUni{+l1, +a1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSkHi{+h1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSkHiEsc{+h1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MSkLo{+l1, +a1, +h1}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MQuote{}, +stack, +goal, +done, +bad}:
      hh
    case 0n SCon{+ch, +tl} Pull.S{Pull.MJump{+r1, +j1}, +stack, +goal, +done, +bad}:
      hh
    case 1n+pp SNil{} Pull.S{Pull.MDone{+s1, +v1}, +stack, +goal, +done, +bad}:
      hh
    case 1n+pp SNil{} Pull.S{Pull.MRest{+s1}, +stack, +goal, +done, +bad}:
      hh
    case 1n+pp SNil{} Pull.S{Pull.MIdle{}, +stack, Pull.GNext{}, +done, False{}}:
      eof_go(tt, stack, done, hst, hh)
    case 1n+pp SNil{} Pull.S{Pull.MIdle{}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, done, True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MIdle{}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{g1}, done, False{}})),
        hh)
    case 1n+pp SNil{} Pull.S{Pull.MIdle{}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{g1}, done, True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MWord{+b1, +n1, +m1}, +stack, Pull.GNext{}, +done, False{}}:
      pgo_inv(tt, pp, "", Pull.word.burst(SNil{}, b1, n1, m1, stack, Pull.GNext{}, False{}),
        wm_go(tt, SNil{}, b1, n1, m1, stack, done, hh), hst)
    case 1n+pp SNil{} Pull.S{Pull.MWord{+b1, +n1, +m1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MWord{b1, n1, m1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MWord{+b1, +n1, +m1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MWord{b1, n1, m1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MWord{+b1, +n1, +m1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MWord{b1, n1, m1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSpan{+c1, +n1}, +stack, Pull.GNext{}, +done, False{}}:
      Unit{}
    case 1n+pp SNil{} Pull.S{Pull.MSpan{+c1, +n1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSpan{c1, n1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSpan{+c1, +n1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSpan{c1, n1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSpan{+c1, +n1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSpan{c1, n1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MCopy{+b1}, +stack, Pull.GNext{}, +done, False{}}:
      Unit{}
    case 1n+pp SNil{} Pull.S{Pull.MCopy{+b1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MCopy{b1}, stack, Pull.GNext{}, done, True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MCopy{+b1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MCopy{b1}, stack, Pull.GSkip{g1}, done, False{}})),
        hh)
    case 1n+pp SNil{} Pull.S{Pull.MCopy{+b1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MCopy{b1}, stack, Pull.GSkip{g1}, done, True{}})),
        hh)
    case 1n+pp SNil{} Pull.S{Pull.MEsc{+b1}, +stack, Pull.GNext{}, +done, False{}}:
      Unit{}
    case 1n+pp SNil{} Pull.S{Pull.MEsc{+b1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MEsc{b1}, stack, Pull.GNext{}, done, True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MEsc{+b1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MEsc{b1}, stack, Pull.GSkip{g1}, done, False{}})),
        hh)
    case 1n+pp SNil{} Pull.S{Pull.MEsc{+b1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MEsc{b1}, stack, Pull.GSkip{g1}, done, True{}})),
        hh)
    case 1n+pp SNil{} Pull.S{Pull.MUni{+l1, +a1, +b1}, +stack, Pull.GNext{}, +done, False{}}:
      Unit{}
    case 1n+pp SNil{} Pull.S{Pull.MUni{+l1, +a1, +b1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MUni{l1, a1, b1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MUni{+l1, +a1, +b1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MUni{l1, a1, b1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MUni{+l1, +a1, +b1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MUni{l1, a1, b1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MHi{+h1, +b1}, +stack, Pull.GNext{}, +done, False{}}:
      Unit{}
    case 1n+pp SNil{} Pull.S{Pull.MHi{+h1, +b1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MHi{h1, b1}, stack, Pull.GNext{}, done, True{}})),
        hh)
    case 1n+pp SNil{} Pull.S{Pull.MHi{+h1, +b1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MHi{h1, b1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MHi{+h1, +b1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MHi{h1, b1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MHiEsc{+h1, +b1}, +stack, Pull.GNext{}, +done, False{}}:
      Unit{}
    case 1n+pp SNil{} Pull.S{Pull.MHiEsc{+h1, +b1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MHiEsc{h1, b1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MHiEsc{+h1, +b1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MHiEsc{h1, b1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MHiEsc{+h1, +b1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MHiEsc{h1, b1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MLo{+l1, +a1, +h1, +b1}, +stack, Pull.GNext{}, +done, False{}}:
      Unit{}
    case 1n+pp SNil{} Pull.S{Pull.MLo{+l1, +a1, +h1, +b1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MLo{l1, a1, h1, b1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MLo{+l1, +a1, +h1, +b1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MLo{l1, a1, h1, b1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MLo{+l1, +a1, +h1, +b1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MLo{l1, a1, h1, b1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkStr{}, +stack, Pull.GNext{}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkStr{}, stack, Pull.GNext{}, done, False{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkStr{}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkStr{}, stack, Pull.GNext{}, done, True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkStr{}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkStr{}, stack, Pull.GSkip{g1}, done, False{}})),
        hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkStr{}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkStr{}, stack, Pull.GSkip{g1}, done, True{}})),
        hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkEsc{}, +stack, Pull.GNext{}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkEsc{}, stack, Pull.GNext{}, done, False{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkEsc{}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkEsc{}, stack, Pull.GNext{}, done, True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkEsc{}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkEsc{}, stack, Pull.GSkip{g1}, done, False{}})),
        hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkEsc{}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkEsc{}, stack, Pull.GSkip{g1}, done, True{}})),
        hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkUni{+l1, +a1}, +stack, Pull.GNext{}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkUni{l1, a1}, stack, Pull.GNext{}, done,
        False{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkUni{+l1, +a1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkUni{l1, a1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkUni{+l1, +a1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkUni{l1, a1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkUni{+l1, +a1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkUni{l1, a1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkHi{+h1}, +stack, Pull.GNext{}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkHi{h1}, stack, Pull.GNext{}, done, False{}})),
        hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkHi{+h1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkHi{h1}, stack, Pull.GNext{}, done, True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkHi{+h1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkHi{h1}, stack, Pull.GSkip{g1}, done, False{}})),
        hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkHi{+h1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkHi{h1}, stack, Pull.GSkip{g1}, done, True{}})),
        hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkHiEsc{+h1}, +stack, Pull.GNext{}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkHiEsc{h1}, stack, Pull.GNext{}, done,
        False{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkHiEsc{+h1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkHiEsc{h1}, stack, Pull.GNext{}, done, True{}})),
        hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkHiEsc{+h1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkHiEsc{h1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkHiEsc{+h1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkHiEsc{h1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkLo{+l1, +a1, +h1}, +stack, Pull.GNext{}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkLo{l1, a1, h1}, stack, Pull.GNext{}, done,
        False{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkLo{+l1, +a1, +h1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkLo{l1, a1, h1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkLo{+l1, +a1, +h1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkLo{l1, a1, h1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MSkLo{+l1, +a1, +h1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MSkLo{l1, a1, h1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MQuote{}, +stack, Pull.GNext{}, +done, False{}}:
      Unit{}
    case 1n+pp SNil{} Pull.S{Pull.MQuote{}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MQuote{}, stack, Pull.GNext{}, done, True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MQuote{}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MQuote{}, stack, Pull.GSkip{g1}, done, False{}})),
        hh)
    case 1n+pp SNil{} Pull.S{Pull.MQuote{}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MQuote{}, stack, Pull.GSkip{g1}, done, True{}})),
        hh)
    case 1n+pp SNil{} Pull.S{Pull.MJump{+r1, +j1}, +stack, Pull.GNext{}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MJump{r1, j1}, stack, Pull.GNext{}, done,
        False{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MJump{+r1, +j1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MJump{r1, j1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MJump{+r1, +j1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MJump{r1, j1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SNil{} Pull.S{Pull.MJump{+r1, +j1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SNil{}, Pull.S{Pull.MJump{r1, j1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MDone{+s1, +v1}, +stack, +goal, +done, +bad}:
      hh
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MRest{+s1}, +stack, +goal, +done, +bad}:
      hh
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MIdle{}, +stack, Pull.GNext{}, +done, False{}}:
      pgo_inv(tt, 1n+pp, tl, Pull.look.plan(ch, stack, Pull.GNext{}, done, Lex.classify(ch)),
        idle_go(tt, ch, tl, stack, done, hh), hst)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MIdle{}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MIdle{}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MIdle{}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MIdle{}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MWord{+b1, +n1, +m1}, +stack, Pull.GNext{}, +done, False{}}:
      pgo_inv(tt, pp, "", Pull.word.burst(SCon{ch, tl}, b1, n1, m1, stack, Pull.GNext{}, False{}),
        wm_go(tt, SCon{ch, tl}, b1, n1, m1, stack, done, hh), hst)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MWord{+b1, +n1, +m1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MWord{b1, n1, m1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MWord{+b1, +n1, +m1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MWord{b1, n1, m1}, stack, Pull.GSkip{g1},
        done, False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MWord{+b1, +n1, +m1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MWord{b1, n1, m1}, stack, Pull.GSkip{g1},
        done, True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSpan{+c1, +n1}, +stack, Pull.GNext{}, +done, False{}}:
      pgo_inv(tt, 1n+pp, tl, Pull.span.advance(Pull.span.kind.of(ch), c1, n1, stack, Pull.GNext{}, done),
        sm_span(tt, ch, tl, c1, n1, stack, done, hh), hst)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSpan{+c1, +n1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSpan{c1, n1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSpan{+c1, +n1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSpan{c1, n1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSpan{+c1, +n1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSpan{c1, n1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MCopy{+b1}, +stack, Pull.GNext{}, +done, False{}}:
      pgo_inv(tt, 1n+pp, tl, Pull.copy.hit(ch, tl, b1, stack, Pull.GNext{}, done, False{}, Lex.classify(ch),
        U32.is_lt(Char.to_u32(ch), 32)),
        sm_copy(tt, ch, tl, b1, stack, done, hh), hst)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MCopy{+b1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MCopy{b1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MCopy{+b1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MCopy{b1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MCopy{+b1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MCopy{b1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MEsc{+b1}, +stack, Pull.GNext{}, +done, False{}}:
      pgo_inv(tt, 1n+pp, tl, Pull.esc.hit(ch, tl, b1, stack, Pull.GNext{}, done, False{}),
        sm_esc(tt, ch, tl, b1, stack, done, hh), hst)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MEsc{+b1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MEsc{b1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MEsc{+b1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MEsc{b1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MEsc{+b1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MEsc{b1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MUni{+l1, +a1, +b1}, +stack, Pull.GNext{}, +done, False{}}:
      pgo_inv(tt, 1n+pp, tl, Pull.uni.hit(ch, tl, l1, a1, b1, stack, Pull.GNext{}, done, False{}),
        sm_uni(tt, ch, tl, l1, a1, b1, stack, done, hh), hst)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MUni{+l1, +a1, +b1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MUni{l1, a1, b1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MUni{+l1, +a1, +b1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MUni{l1, a1, b1}, stack, Pull.GSkip{g1},
        done, False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MUni{+l1, +a1, +b1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MUni{l1, a1, b1}, stack, Pull.GSkip{g1},
        done, True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MHi{+h1, +b1}, +stack, Pull.GNext{}, +done, False{}}:
      pgo_inv(tt, 1n+pp, tl, Pull.hi.hit(tl, h1, b1, stack, Pull.GNext{}, done, False{}, Lex.classify(ch)),
        sm_hi(tt, ch, tl, h1, b1, stack, done, hh), hst)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MHi{+h1, +b1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MHi{h1, b1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MHi{+h1, +b1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MHi{h1, b1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MHi{+h1, +b1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MHi{h1, b1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MHiEsc{+h1, +b1}, +stack, Pull.GNext{}, +done, False{}}:
      pgo_inv(tt, 1n+pp, tl, Pull.hiesc.hit(ch, tl, h1, b1, stack, Pull.GNext{}, done, False{}),
        sm_hiesc(tt, ch, tl, h1, b1, stack, done, hh), hst)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MHiEsc{+h1, +b1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MHiEsc{h1, b1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MHiEsc{+h1, +b1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MHiEsc{h1, b1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MHiEsc{+h1, +b1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MHiEsc{h1, b1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MLo{+l1, +a1, +h1, +b1}, +stack, Pull.GNext{}, +done, False{}}:
      pgo_inv(tt, 1n+pp, tl, Pull.lo.hit(ch, tl, l1, a1, h1, b1, stack, Pull.GNext{}, done, False{}),
        sm_lo(tt, ch, tl, l1, a1, h1, b1, stack, done, hh), hst)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MLo{+l1, +a1, +h1, +b1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MLo{l1, a1, h1, b1}, stack, Pull.GNext{},
        done, True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MLo{+l1, +a1, +h1, +b1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MLo{l1, a1, h1, b1}, stack, Pull.GSkip{g1},
        done, False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MLo{+l1, +a1, +h1, +b1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MLo{l1, a1, h1, b1}, stack, Pull.GSkip{g1},
        done, True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkStr{}, +stack, Pull.GNext{}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkStr{}, stack, Pull.GNext{}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkStr{}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkStr{}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkStr{}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkStr{}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkStr{}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkStr{}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkEsc{}, +stack, Pull.GNext{}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkEsc{}, stack, Pull.GNext{}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkEsc{}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkEsc{}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkEsc{}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkEsc{}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkEsc{}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkEsc{}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkUni{+l1, +a1}, +stack, Pull.GNext{}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkUni{l1, a1}, stack, Pull.GNext{}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkUni{+l1, +a1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkUni{l1, a1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkUni{+l1, +a1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkUni{l1, a1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkUni{+l1, +a1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkUni{l1, a1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkHi{+h1}, +stack, Pull.GNext{}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkHi{h1}, stack, Pull.GNext{}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkHi{+h1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkHi{h1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkHi{+h1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkHi{h1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkHi{+h1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkHi{h1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkHiEsc{+h1}, +stack, Pull.GNext{}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkHiEsc{h1}, stack, Pull.GNext{}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkHiEsc{+h1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkHiEsc{h1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkHiEsc{+h1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkHiEsc{h1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkHiEsc{+h1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkHiEsc{h1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkLo{+l1, +a1, +h1}, +stack, Pull.GNext{}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkLo{l1, a1, h1}, stack, Pull.GNext{}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkLo{+l1, +a1, +h1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkLo{l1, a1, h1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkLo{+l1, +a1, +h1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkLo{l1, a1, h1}, stack, Pull.GSkip{g1},
        done, False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MSkLo{+l1, +a1, +h1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MSkLo{l1, a1, h1}, stack, Pull.GSkip{g1},
        done, True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MQuote{}, +stack, Pull.GNext{}, +done, False{}}:
      pgo_inv(tt, 1n+pp, tl, Pull.quote.first(ch, tl, stack, Pull.GNext{}, done),
        sm_quote(tt, ch, tl, stack, done, hh), hst)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MQuote{}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MQuote{}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MQuote{}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MQuote{}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MQuote{}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MQuote{}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MJump{+r1, +j1}, +stack, Pull.GNext{}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MJump{r1, j1}, stack, Pull.GNext{}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MJump{+r1, +j1}, +stack, Pull.GNext{}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MJump{r1, j1}, stack, Pull.GNext{}, done,
        True{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MJump{+r1, +j1}, +stack, Pull.GSkip{+g1}, +done, False{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MJump{r1, j1}, stack, Pull.GSkip{g1}, done,
        False{}})), hh)
    case 1n+pp SCon{+ch, +tl} Pull.S{Pull.MJump{+r1, +j1}, +stack, Pull.GSkip{+g1}, +done, True{}}:
      Empty.absurd(oinv(tt, Pull.next.go(1n+pp, SCon{ch, tl}, Pull.S{Pull.MJump{r1, j1}, stack, Pull.GSkip{g1}, done,
        True{}})), hh)

# a walk's levels keep it in step
law prun_inv:
  for +tt: String
  for +lvl: Nat
  for oo: Pull.Out
  for hh: oinv(tt, oo)
  for +hst: {D1.short(tt) == True{} : Bool}
  oinv(tt, Pull.next.run(lvl, oo))

def prun_inv(tt, lvl, oo, hh, hst):
  match lvl oo:
    case 0n Pull.More{+txt, +st}:
      pgo_inv(tt, 4n, txt, st, hh, hst)
    case 1n+pp Pull.More{+txt, +st}:
      prun_inv(tt, pp, Pull.next.run(pp, Pull.More{txt, st}), prun_inv(tt, pp, Pull.More{txt, st}, hh, hst), hst)
    case 0n Pull.Fin{_}:
      hh
    case 1n+pp Pull.Fin{_}:
      hh

# a walk's growing budget keeps it in step
law pgrow_inv:
  for +tt: String
  for +left: Nat
  for +lvl: Nat
  for oo: Pull.Out
  for hh: oinv(tt, oo)
  for +hst: {D1.short(tt) == True{} : Bool}
  oinv(tt, Pull.next.grow(left, lvl, oo))

def pgrow_inv(tt, left, lvl, oo, hh, hst):
  match left oo:
    case 1n+pp Pull.More{+txt, +st}:
      pgrow_inv(tt, pp, 1n+lvl, Pull.next.run(lvl, Pull.More{txt, st}), prun_inv(tt, lvl, Pull.More{txt, st}, hh, hst),
        hst)
    case 0n Pull.More{_, _}:
      hh
    case 1n+pp Pull.Fin{_}:
      hh
    case 0n Pull.Fin{_}:
      hh

# a walk's answer in step
law pfin_inv:
  for +tt: String
  for oo: Pull.Out
  for hh: oinv(tt, oo)
  fok2(tt, Pull.next.fin(oo))

def pfin_inv(_tt, oo, hh):
  match oo:
    case Pull.Fin{_}:
      hh
    case Pull.More{_, _}:
      Unit{}

# a step's answer in step, handed out by next
law use_inv:
  for +tt: String
  for got: (Pull.Stop & Pull.Cur)
  for hh: fok2(tt, got)
  M6.post(tt, Pull.next.use(got))

def use_inv(_tt, got, hh):
  match got:
    case (Pull.SEv{Pull.EErr{}}, _):
      {==}
    case (Pull.SEv{Pull.EEnd{}}, _):
      hh
    case (Pull.SSkip{}, _):
      {==}
    case (Pull.SEv{Pull.ENull{}}, _):
      hh
    case (Pull.SEv{Pull.EBool{+x1}}, _):
      hh
    case (Pull.SEv{Pull.ENum{+x1, +x2}}, _):
      hh
    case (Pull.SEv{Pull.EStr{+x1}}, _):
      hh
    case (Pull.SEv{Pull.EStrS{+x1, +x2}}, _):
      hh
    case (Pull.SEv{Pull.EKey{+x1}}, _):
      hh
    case (Pull.SEv{Pull.EKeyS{+x1, +x2}}, _):
      hh
    case (Pull.SEv{Pull.EBeginArr{}}, _):
      hh
    case (Pull.SEv{Pull.EEndArr{}}, _):
      hh
    case (Pull.SEv{Pull.EBeginObj{}}, _):
      hh
    case (Pull.SEv{Pull.EEndObj{}}, _):
      hh

# next on a cursor in step
law next_inv:
  for +tt: String
  for +cur: Pull.Cur
  for hh: M6.cinv(tt, cur)
  for +hst: {D1.short(tt) == True{} : Bool}
  M6.post(tt, Ezjson.next(cur))

def next_inv(tt, cur, hh, hst):
  match cur:
    case Pull.Cur{+rest, +stack, +done, False{}}:
      use_inv(tt, Pull.next.walk(rest, Pull.S{Pull.MIdle{}, stack, Pull.GNext{}, done, False{}}),
        pfin_inv(tt, Pull.next.grow(Pull.next.levels(), 0n, Pull.More{rest, Pull.S{Pull.MIdle{}, stack, Pull.GNext{},
          done,
          False{}}}), pgrow_inv(tt, Pull.next.levels(), 0n, Pull.More{rest, Pull.S{Pull.MIdle{}, stack, Pull.GNext{},
            done,
          False{}}}, hh, hst)))
    case Pull.Cur{_, _, _, True{}}:
      Empty.absurd(M6.post(tt, Ezjson.next(cur)), hh)

# a failed cursor fails for good
law nexts_failed:
  for +kk: Nat
  {D1.nexts(kk, Pull.Cur{"", [], False{}, True{}}) == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}

def nexts_failed(kk):
  match kk:
    case 0n:
      {==}
    case 1n+pp:
      nexts_failed(pp)

# the event after one call of next and more, once that call's answer is in hand
law ends_at:
  for +tt: String
  for +kk: Nat
  for rr: (Pull.Ev & Pull.Cur)
  for hp: M6.post(tt, rr)
  for he: {D1.is_end(D1.ev_of(Ezjson.next(D1.nexts(kk, D1.cur_of(rr))))) == True{} : Bool}
  for ih: @cc: Pull.Cur -> M6.cinv(tt, cc) -> {D1.is_end(D1.ev_of(Ezjson.next(D1.nexts(kk,
    cc)))) == True{} : Bool} ->
    {D1.is_some(Ezjson.parse(tt)) == True{} : Bool}
  {D1.is_some(Ezjson.parse(tt)) == True{} : Bool}

def ends_at(tt, kk, rr, hp, he, ih):
  match rr:
    case (Pull.EErr{}, +cur):
      ef = Equal.sym(Pull.Cur, cur, Pull.Cur{"", [], False{}, True{}}, hp)
      M6.no({D1.is_some(Ezjson.parse(tt)) == True{} : Bool}, Equal.trans(Bool, False{},
        D1.is_end(D1.ev_of(Ezjson.next(D1.nexts(kk, Pull.Cur{"", [], False{}, True{}})))), True{},
        Equal.cong(Pull.Cur, Bool, zz => D1.is_end(D1.ev_of(Ezjson.next(zz))), Pull.Cur{"", [], False{}, True{}},
          D1.nexts(kk, Pull.Cur{"", [], False{}, True{}}), Equal.sym(Pull.Cur, D1.nexts(kk, Pull.Cur{"", [],
            False{},
          True{}}), Pull.Cur{"", [], False{}, True{}}, nexts_failed(kk))),
        Equal.trans(Bool, D1.is_end(D1.ev_of(Ezjson.next(D1.nexts(kk, Pull.Cur{"", [], False{}, True{}})))),
          D1.is_end(D1.ev_of(Ezjson.next(D1.nexts(kk, cur)))), True{}, Equal.cong(Pull.Cur, Bool,
          zz => D1.is_end(D1.ev_of(Ezjson.next(D1.nexts(kk, zz)))), Pull.Cur{"", [], False{}, True{}}, cur, ef),
          he)))
    case (Pull.EEnd{}, _):
      hp
    case (Pull.ENull{}, +cur):
      ih(cur, hp, he)
    case (Pull.EBool{+x1}, +cur):
      ih(cur, hp, he)
    case (Pull.ENum{+x1, +x2}, +cur):
      ih(cur, hp, he)
    case (Pull.EStr{+x1}, +cur):
      ih(cur, hp, he)
    case (Pull.EStrS{+x1, +x2}, +cur):
      ih(cur, hp, he)
    case (Pull.EKey{+x1}, +cur):
      ih(cur, hp, he)
    case (Pull.EKeyS{+x1, +x2}, +cur):
      ih(cur, hp, he)
    case (Pull.EBeginArr{}, +cur):
      ih(cur, hp, he)
    case (Pull.EEndArr{}, +cur):
      ih(cur, hp, he)
    case (Pull.EBeginObj{}, +cur):
      ih(cur, hp, he)
    case (Pull.EEndObj{}, +cur):
      ih(cur, hp, he)

# the first call of next, when it is the end
law ends_now:
  for +tt: String
  for rr: (Pull.Ev & Pull.Cur)
  for hp: M6.post(tt, rr)
  for he: {D1.is_end(D1.ev_of(rr)) == True{} : Bool}
  {D1.is_some(Ezjson.parse(tt)) == True{} : Bool}

def ends_now(tt, rr, hp, he):
  match rr:
    case (Pull.EEnd{}, _):
      hp
    case (Pull.EErr{}, _):
      M6.no({D1.is_some(Ezjson.parse(tt)) == True{} : Bool}, he)
    case (Pull.ENull{}, _):
      M6.no({D1.is_some(Ezjson.parse(tt)) == True{} : Bool}, he)
    case (Pull.EBool{+x1}, _):
      M6.no({D1.is_some(Ezjson.parse(tt)) == True{} : Bool}, he)
    case (Pull.ENum{+x1, +x2}, _):
      M6.no({D1.is_some(Ezjson.parse(tt)) == True{} : Bool}, he)
    case (Pull.EStr{+x1}, _):
      M6.no({D1.is_some(Ezjson.parse(tt)) == True{} : Bool}, he)
    case (Pull.EStrS{+x1, +x2}, _):
      M6.no({D1.is_some(Ezjson.parse(tt)) == True{} : Bool}, he)
    case (Pull.EKey{+x1}, _):
      M6.no({D1.is_some(Ezjson.parse(tt)) == True{} : Bool}, he)
    case (Pull.EKeyS{+x1, +x2}, _):
      M6.no({D1.is_some(Ezjson.parse(tt)) == True{} : Bool}, he)
    case (Pull.EBeginArr{}, _):
      M6.no({D1.is_some(Ezjson.parse(tt)) == True{} : Bool}, he)
    case (Pull.EEndArr{}, _):
      M6.no({D1.is_some(Ezjson.parse(tt)) == True{} : Bool}, he)
    case (Pull.EBeginObj{}, _):
      M6.no({D1.is_some(Ezjson.parse(tt)) == True{} : Bool}, he)
    case (Pull.EEndObj{}, _):
      M6.no({D1.is_some(Ezjson.parse(tt)) == True{} : Bool}, he)

# a cursor in step whose events reach the end: its text parses
law ends_parse:
  for +tt: String
  for +kk: Nat
  for +cur: Pull.Cur
  for hc: M6.cinv(tt, cur)
  for +hst: {D1.short(tt) == True{} : Bool}
  for he: {D1.is_end(D1.ev_of(Ezjson.next(D1.nexts(kk, cur)))) == True{} : Bool}
  {D1.is_some(Ezjson.parse(tt)) == True{} : Bool}

def ends_parse(tt, kk, cur, hc, hst, he):
  match kk:
    case 0n:
      ends_now(tt, Ezjson.next(cur), next_inv(tt, cur, hc, hst), he)
    case 1n+pp:
      ends_at(tt, pp, Ezjson.next(cur), next_inv(tt, cur, hc, hst), he, +cc => hcc => hee => ends_parse(tt, pp, cc, hcc,
        hst, hee))

# the events from a text's cursor reach the end only when the text parses
law pull_end:
  for +txt: String
  for +kk: Nat
  for +h_s: {D1.short(txt) == True{} : Bool}
  for he: {D1.is_end(D1.ev_of(Ezjson.next(D1.nexts(kk, Ezjson.cursor(txt))))) == True{} : Bool}
  {D1.is_some(Ezjson.parse(txt)) == True{} : Bool}

def pull_end(txt, kk, h_s, he):
  ends_parse(txt, kk, Ezjson.cursor(txt), (h_s, (M6.lx0(), ({==}, ({==}, {==})))), h_s, he)

def Laws.pull_events(txt, jj, h_s, h_p):
  pull_ev(txt, jj, h_s, h_p)

def Laws.pull_ends(txt, kk, h_s, h_e):
  pull_end(txt, kk, h_s, h_e)
