# the character lexer after a value's text: punctuation and whitespace
import Base
import ../../src/value.bend as V
import ../../src/lex.bend as Lex
import ../../src/pull.bend as Pull
import ./LexemeOrder.bend as M1
import ./WellFormedCells.bend as M2

# whitespace, once whether the code is 13 is known
law ws_d:
  for +uu: U32
  for bb: Bool
  for eb: {U32.is_eq(uu, 13) == bb : Bool}
  for h_ws: {bb == True{} : Bool}
  {Lex.classify(Chr{uu}) == Lex.CSpace{} : Lex.Class}

def ws_d(uu, bb, eb, h_ws):
  match bb:
    case True{}:
      ek = Equal.sym(U32, uu, 13, M2.ueq(uu, 13, eb))
      %ek : {Lex.classify(Chr{_}) == Lex.CSpace{} : Lex.Class}
      {==}
    case False{}:
      Empty.absurd({Lex.classify(Chr{uu}) == Lex.CSpace{} : Lex.Class}, M1.false_true(h_ws))

# whitespace, once whether the code is 10 is known
law ws_c:
  for +uu: U32
  for bb: Bool
  for eb: {U32.is_eq(uu, 10) == bb : Bool}
  for h_ws: {Bool.or(bb, U32.is_eq(uu, 13)) == True{} : Bool}
  {Lex.classify(Chr{uu}) == Lex.CSpace{} : Lex.Class}

def ws_c(uu, bb, eb, h_ws):
  match bb:
    case True{}:
      ek = Equal.sym(U32, uu, 10, M2.ueq(uu, 10, eb))
      %ek : {Lex.classify(Chr{_}) == Lex.CSpace{} : Lex.Class}
      {==}
    case False{}:
      ws_d(uu, U32.is_eq(uu, 13), {==}, h_ws)

# whitespace, once whether the code is 9 is known
law ws_b:
  for +uu: U32
  for bb: Bool
  for eb: {U32.is_eq(uu, 9) == bb : Bool}
  for h_ws: {Bool.or(bb, Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13))) == True{} : Bool}
  {Lex.classify(Chr{uu}) == Lex.CSpace{} : Lex.Class}

def ws_b(uu, bb, eb, h_ws):
  match bb:
    case True{}:
      ek = Equal.sym(U32, uu, 9, M2.ueq(uu, 9, eb))
      %ek : {Lex.classify(Chr{_}) == Lex.CSpace{} : Lex.Class}
      {==}
    case False{}:
      ws_c(uu, U32.is_eq(uu, 10), {==}, h_ws)

# whitespace, once whether the code is 32 is known
law ws_a:
  for +uu: U32
  for bb: Bool
  for eb: {U32.is_eq(uu, 32) == bb : Bool}
  for h_ws: {Bool.or(bb, Bool.or(U32.is_eq(uu, 9), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)))) == True{} : Bool}
  {Lex.classify(Chr{uu}) == Lex.CSpace{} : Lex.Class}

def ws_a(uu, bb, eb, h_ws):
  match bb:
    case True{}:
      ek = Equal.sym(U32, uu, 32, M2.ueq(uu, 32, eb))
      %ek : {Lex.classify(Chr{_}) == Lex.CSpace{} : Lex.Class}
      {==}
    case False{}:
      ws_b(uu, U32.is_eq(uu, 9), {==}, h_ws)

# a finished step returns its answer, whatever text is left
law go_done:
  for +ff: Nat
  for +txt: String
  for stop: Pull.Stop
  for saved: String
  for stack: List<&2, Pull.Frame>
  for goal: Pull.Goal
  for done: Bool
  for bad: Bool
  {Pull.next.go(1n+ff, txt, Pull.S{Pull.MDone{stop, saved}, stack, goal, done, bad})
    == Pull.Fin{(stop, Pull.Cur{saved, stack, done, bad})} : Pull.Out}

def go_done(_ff, txt, _stop, _saved, _stack, _goal, _done, _bad):
  match txt:
    case SNil{}:
      {==}
    case SCon{_, _}:
      {==}

# the character lexer's state after a value's text, from between tokens: a
# word still open, or the value's tokens pushed
def pend(val: V.Json, acc: List<&2, Lex.Tok>) -> Lex.Lex:
  match val:
    case V.JNull{}:
      Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, String.to_list("null"), []), acc}
    case V.JBool{bb}:
      match bb:
        case True{}:
          Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, String.to_list("true"), []), acc}
        case False{}:
          Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, String.to_list("false"), []), acc}
    case V.JNum{raw}:
      Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, String.to_list(raw), []), acc}
    case V.JStr{a1}:
      Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M1.tj(V.JStr{a1}, V.WVal{}), acc)}
    case V.JArr{a1}:
      Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M1.tj(V.JArr{a1}, V.WVal{}), acc)}
    case V.JObj{a1}:
      Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M1.tj(V.JObj{a1}, V.WVal{}), acc)}
    case V.JNil{}:
      Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M1.tj(V.JNil{}, V.WVal{}), acc)}
    case V.JCons{a1, a2}:
      Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M1.tj(V.JCons{a1, a2}, V.WVal{}), acc)}
    case V.JPair{a1, a2, a3}:
      Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M1.tj(V.JPair{a1, a2, a3}, V.WVal{}), acc)}
    case V.JSpan{a1, a2}:
      Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M1.tj(V.JSpan{a1, a2}, V.WVal{}), acc)}
    case V.JBind{a1, a2, a3, a4}:
      Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M1.tj(V.JBind{a1, a2, a3, a4}, V.WVal{}), acc)}

# a punctuation character after a value's text pushes its tokens, then its own
law close:
  for +val: V.Json
  for +ch: Char
  for +tt: Lex.Tok
  for ec: {Lex.classify(ch) == Lex.CPunct{tt} : Lex.Class}
  for +acc: List<&2, Lex.Tok>
  {Lex.feed(ch, pend(val, acc)) ==
    Lex.Lex{Lex.Idle{}, [], tt <> List.reverse.go(&2, Lex.Tok, M1.tj(val, V.WVal{}), acc)} : Lex.Lex}

def close(val, ch, tt, ec, acc):
  match val:
    case V.JNull{}:
      M1.feed_as(ch, Lex.Word{}, List.reverse.go(&2, Char, String.to_list("null"), []), acc, Lex.CPunct{tt}, ec)
    case V.JBool{bb}:
      match bb:
        case True{}:
          M1.feed_as(ch, Lex.Word{}, List.reverse.go(&2, Char, String.to_list("true"), []), acc, Lex.CPunct{tt}, ec)
        case False{}:
          M1.feed_as(ch, Lex.Word{}, List.reverse.go(&2, Char, String.to_list("false"), []), acc, Lex.CPunct{tt}, ec)
    case V.JNum{+raw}:
      +bf = List.reverse.go(&2, Char, String.to_list(raw), [])
      Equal.trans(Lex.Lex, Lex.feed(ch, Lex.Lex{Lex.Word{}, bf, acc}),
        Lex.Lex{Lex.Idle{}, [], tt <> Lex.TWord{Lex.text(bf)} <> acc},
        Lex.Lex{Lex.Idle{}, [], tt <> Lex.TWord{raw} <> acc},
        M1.feed_as(ch, Lex.Word{}, bf, acc, Lex.CPunct{tt}, ec),
        Equal.cong(String, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], tt <> Lex.TWord{xx} <> acc}, Lex.text(bf), raw,
          M1.word_text(raw)))
    case V.JStr{a1}:
      M1.feed_as(ch, Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M1.tj(V.JStr{a1}, V.WVal{}), acc), Lex.CPunct{tt}, ec)
    case V.JArr{a1}:
      M1.feed_as(ch, Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M1.tj(V.JArr{a1}, V.WVal{}), acc), Lex.CPunct{tt}, ec)
    case V.JObj{a1}:
      M1.feed_as(ch, Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M1.tj(V.JObj{a1}, V.WVal{}), acc), Lex.CPunct{tt}, ec)
    case V.JNil{}:
      M1.feed_as(ch, Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M1.tj(V.JNil{}, V.WVal{}), acc), Lex.CPunct{tt}, ec)
    case V.JCons{a1, a2}:
      M1.feed_as(ch, Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M1.tj(V.JCons{a1, a2}, V.WVal{}), acc),
          Lex.CPunct{tt}, ec)
    case V.JPair{a1, a2, a3}:
      M1.feed_as(ch, Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M1.tj(V.JPair{a1, a2, a3}, V.WVal{}), acc),
          Lex.CPunct{tt},
        ec)
    case V.JSpan{a1, a2}:
      M1.feed_as(ch, Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M1.tj(V.JSpan{a1, a2}, V.WVal{}), acc),
          Lex.CPunct{tt}, ec)
    case V.JBind{a1, a2, a3, a4}:
      M1.feed_as(ch, Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M1.tj(V.JBind{a1, a2, a3, a4}, V.WVal{}), acc),
        Lex.CPunct{tt}, ec)
