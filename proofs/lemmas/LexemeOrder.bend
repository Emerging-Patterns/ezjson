# lexemes with the whitespace before them, and boolean and facts
import Base
import ../../src/value.bend as V
import ../../main.bend as Ezjson
import ../../src/lazy.bend as Lazy
import ../../src/lex.bend as Lex
import ../../src/parse.bend as Parse
import ../../src/print.bend as Print
import ../../src/pull.bend as Pull
import ../../laws/defs/CursorAndNumberRules.bend as D1
import ../../laws/defs/GrammarDerivations.bend as D2

# Unit for False, Empty for True
def false_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Unit
    case True{}:
      Empty

# False is never True
law false_true:
  for e: {False{} == True{} : Bool}
  Empty

def false_true(e):
  %e : false_ty(_)
  Unit{}

# both sides of a true and: the left
law and_left:
  for aa: Bool
  for -bb: Bool
  for h_and: {Bool.and(aa, bb) == True{} : Bool}
  {aa == True{} : Bool}

def and_left(aa, _bb, h_and):
  match aa:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(h_and))

# both sides of a true and: the right
law and_right:
  for aa: Bool
  for -bb: Bool
  for h_and: {Bool.and(aa, bb) == True{} : Bool}
  {bb == True{} : Bool}

def and_right(aa, _bb, h_and):
  match aa:
    case True{}:
      h_and
    case False{}:
      Empty.absurd({_bb == True{} : Bool}, false_true(h_and))

# both sides of a true and, from one proof
law and_both:
  for aa: Bool
  for -bb: Bool
  for h_and: {Bool.and(aa, bb) == True{} : Bool}
  ({aa == True{} : Bool} & {bb == True{} : Bool})

def and_both(aa, bb, h_and):
  match aa:
    case True{}:
      ({==}, h_and)
    case False{}:
      Empty.absurd(({False{} == True{} : Bool} & {bb == True{} : Bool}), false_true(h_and))

# a token with a span replaced by the characters it covers
def den(tok: Lex.Tok) -> Lex.Tok:
  match tok:
    case Lex.TStrS{cut, +nn}:
      Lex.TStr{V.span.str(cut, nn, U32.is_zero(nn))}
    case Lex.TWordS{cut, +nn}:
      Lex.TWord{V.span.str(cut, nn, U32.is_zero(nn))}
    case other:
      other

# tokens with their spans replaced
def dens(toks: List<&2, Lex.Tok>) -> List<&2, Lex.Tok>:
  match toks:
    case Nil{}:
      Nil{}
    case hd <> tl:
      den(hd) <> dens(tl)

# appending nothing
law append_nil:
  for +txt: String
  {txt ++ "" == txt : String}

def append_nil(txt):
  match txt:
    case SNil{}:
      {==}
    case SCon{hd, tl}:
      Equal.cong(String, String, xx => SCon{hd, xx}, tl ++ "", tl, append_nil(tl))

# feed, with the character's class named
law feed_as:
  for +ch: Char
  for md: Lex.Mode
  for bf: List<&2, Char>
  for tk: List<&2, Lex.Tok>
  for cls: Lex.Class
  for ecls: {Lex.classify(ch) == cls : Lex.Class}
  {Lex.feed(ch, Lex.Lex{md, bf, tk}) == Lex.step(md, cls, ch, bf, tk) : Lex.Lex}

def feed_as(ch, md, bf, tk, cls, ecls):
  ec = Equal.sym(Lex.Class, Lex.classify(ch), cls, ecls)
  %ec : {Lex.step(md, _, ch, bf, tk) == Lex.step(md, cls, ch, bf, tk) : Lex.Lex}
  {==}

# a character as print writes it back: itself when a scalar value, else U+FFFD
def fix(ch: Char) -> Char:
  match ch:
    case Chr{+uu}:
      Bool.pick(Char, Print.scalar(uu), Chr{uu}, Chr{65533})

# the characters, fixed, as a string
def fixs(cs: List<&2, Char>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{hd, tl}:
      SCon{fix(hd), fixs(tl)}

# False is never True, at any type
law no:
  for pp: Type
  for h: {False{} == True{} : Bool}
  pp

def no(pp, h):
  Empty.absurd(pp, false_true(h))

# a string's characters, listed then gathered, are the string
law from_to:
  for +txt: String
  {String.from_list(String.to_list(txt)) == txt : String}

def from_to(txt):
  match txt:
    case SNil{}:
      {==}
    case SCon{hd, tl}:
      Equal.cong(String, String, xx => SCon{hd, xx}, String.from_list(String.to_list(tl)), tl, from_to(tl))

# a buffer of reversed characters, read back
law text_revgo:
  for +cs: List<&2, Char>
  for +buf: List<&2, Char>
  for +acc: String
  {Lex.text.go(List.reverse.go(&2, Char, cs, buf), acc) == Lex.text.go(buf, String.from_list(cs) ++ acc) : String}

def text_revgo(cs, buf, acc):
  match cs:
    case Nil{}:
      {==}
    case Con{+hd, +tl}:
      text_revgo(tl, hd <> buf, acc)

# a word's buffer reads back as the word
law word_text:
  for +raw: String
  {Lex.text(List.reverse.go(&2, Char, String.to_list(raw), [])) == raw : String}

def word_text(raw):
  +fl = String.from_list(String.to_list(raw))
  Equal.trans(String, Lex.text.go(List.reverse.go(&2, Char, String.to_list(raw), []), ""), fl ++ "", raw,
    text_revgo(String.to_list(raw), [], ""),
    Equal.trans(String, fl ++ "", fl, raw, append_nil(fl), from_to(raw)))

# the tokens a value is, read straight off it: by shape, a value, an array's
# cells, or an object's cells. Strings are fixed as print writes them
def tj(val: V.Json, sh: V.Shape) -> List<&2, Lex.Tok>:
  match val sh:
    case V.JNull{} V.WVal{}:
      [Lex.TWord{"null"}]
    case V.JBool{True{}} V.WVal{}:
      [Lex.TWord{"true"}]
    case V.JBool{False{}} V.WVal{}:
      [Lex.TWord{"false"}]
    case V.JNum{raw} V.WVal{}:
      [Lex.TWord{raw}]
    case V.JStr{txt} V.WVal{}:
      [Lex.TStr{fixs(String.to_list(txt))}]
    case V.JSpan{src, +nn} V.WVal{}:
      [Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))}]
    case V.JArr{items} V.WVal{}:
      Lex.TOpenArr{} <> List.append(&2, Lex.Tok, tj(items, V.WArr{}), [Lex.TCloseArr{}])
    case V.JObj{pairs} V.WVal{}:
      Lex.TOpenObj{} <> List.append(&2, Lex.Tok, tj(pairs, V.WObj{}), [Lex.TCloseObj{}])
    case V.JNil{} V.WArr{}:
      []
    case V.JCons{hd, V.JNil{}} V.WArr{}:
      tj(hd, V.WVal{})
    case V.JCons{hd, tl} V.WArr{}:
      List.append(&2, Lex.Tok, tj(hd, V.WVal{}), Lex.TComma{} <> tj(tl, V.WArr{}))
    case V.JNil{} V.WObj{}:
      []
    case V.JPair{kk, vv, V.JNil{}} V.WObj{}:
      Lex.TStr{fixs(String.to_list(kk))} <> Lex.TColon{} <> tj(vv, V.WVal{})
    case V.JPair{kk, vv, rr} V.WObj{}:
      Lex.TStr{fixs(String.to_list(kk))} <> Lex.TColon{} <>
        List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(rr, V.WObj{}))
    case V.JBind{src, +nn, vv, V.JNil{}} V.WObj{}:
      Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> Lex.TColon{} <> tj(vv, V.WVal{})
    case V.JBind{src, +nn, vv, rr} V.WObj{}:
      Lex.TStr{fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> Lex.TColon{} <>
        List.append(&2, Lex.Tok, tj(vv, V.WVal{}), Lex.TComma{} <> tj(rr, V.WObj{}))
    case _ _:
      []

# a true early exit: its test held
law stop_l:
  for aa: Bool
  for -bb: Bool
  for h: {Lazy.stop(Bool, Bool.not(aa), False{}, _u => bb) == True{} : Bool}
  {aa == True{} : Bool}

def stop_l(aa, _bb, h):
  match aa:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(h))

# a true early exit: the rest held
law stop_r:
  for aa: Bool
  for -bb: Bool
  for h: {Lazy.stop(Bool, Bool.not(aa), False{}, _u => bb) == True{} : Bool}
  {bb == True{} : Bool}

def stop_r(aa, bb, h):
  match aa:
    case True{}:
      h
    case False{}:
      Empty.absurd({bb == True{} : Bool}, false_true(h))

# `]` after an array's cells and a value
law close_arr_comma:
  for +items: V.Json
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  {Parse.close_arr(Parse.FArr{items, Parse.SComma{}} <> stk, root, bad) ==
    Parse.put(stk, root, V.JArr{V.reverse(items, V.JNil{})}, bad) : Parse.P}

def close_arr_comma(items, _stk, _root, _bad):
  match items:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      {==}
    case V.JArr{+x1}:
      {==}
    case V.JObj{+x1}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      {==}
    case V.JPair{+x1, +x2, +x3}:
      {==}
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      {==}

# `}` after an object's cells and a value
law close_obj_comma:
  for +pairs: V.Json
  for +key: Parse.Key
  for +stk: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +bad: Bool
  {Parse.close_obj(Parse.FObj{pairs, key, Parse.SComma{}} <> stk, root, bad) ==
    Parse.put(stk, root, V.JObj{V.reverse(pairs, V.JNil{})}, bad) : Parse.P}

def close_obj_comma(pairs, _key, _stk, _root, _bad):
  match pairs:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      {==}
    case V.JArr{+x1}:
      {==}
    case V.JObj{+x1}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      {==}
    case V.JPair{+x1, +x2, +x3}:
      {==}
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      {==}

# whether a class is Lex.COther{}
def is_other(cls: Lex.Class) -> Bool:
  match cls:
    case Lex.COther{}:
      True{}
    case _:
      False{}

# a parse result succeeded exactly when its owned form did
law some_own:
  for mb: Maybe<&2, V.Json>
  {D1.is_some(D1.own_m(mb)) == D1.is_some(mb) : Bool}

def some_own(mb):
  match mb:
    case None{}:
      {==}
    case Some{_jj}:
      {==}

# the tokens a state holds, its word pushed when it is inside one
def fl(st: Lex.Lex) -> List<&2, Lex.Tok>:
  match st:
    case Lex.Lex{Lex.Word{}, bf, toks}:
      Lex.TWord{Lex.text(bf)} <> toks
    case Lex.Lex{_, _, toks}:
      toks

# laws/ParsesExactlyJsonTexts.bend: a text the character lexer reads without failing is lexemes

# a lexeme: a punctuation character, a word, or a string's pieces
type Lx is Data:
  LP{ch: Char}
  LW{w: String}
  LS{ps: List<&2, D2.Piece>}

# a lexeme and the whitespace before it, reversed
type It is Data:
  It{rws: List<&2, Char>, lx: Lx}

# a lexeme's characters, reversed onto acc
def rlx(lx: Lx, acc: List<&2, Char>) -> List<&2, Char>:
  match lx:
    case LP{ch}:
      ch <> acc
    case LW{w}:
      List.reverse.go(&2, Char, String.to_list(w), acc)
    case LS{ps}:
      '"' <> List.reverse.go(&2, Char, String.to_list(D2.spell(ps)), '"' <> acc)

# both are true
law and2:
  for aa: Bool
  for bb: Bool
  for ha: {aa == True{} : Bool}
  for hb: {bb == True{} : Bool}
  {Bool.and(aa, bb) == True{} : Bool}

def and2(aa, bb, ha, hb):
  match aa:
    case True{}:
      hb
    case False{}:
      no({Bool.and(False{}, bb) == True{} : Bool}, ha)

# lexemes listed first first, their whitespace and characters reversed onto acc
def fr(its: List<&2, It>, acc: List<&2, Char>) -> List<&2, Char>:
  match its:
    case Nil{}:
      acc
    case It{rws, lx} <> rest:
      fr(rest, rlx(lx, List.append(&2, Char, rws, acc)))

# laws/CursorEventsMatchParse.bend, words

# a text that is empty or starts with a character that ends a word
def stops(txt: String) -> Bool:
  match txt:
    case SNil{}:
      True{}
    case SCon{ch, _}:
      Bool.not(is_other(Lex.classify(ch)))

# laws/CursorEventsMatchParse.bend, the other way: the cursor's events end in EEnd only on a text
# that parses. The cursor is walked in step with the character lexer and the
# parser on the lexer's tokens: while the cursor has not failed, neither have
# they, and they are in the same place

# the character lexer's start
def lx0() -> Lex.Lex:
  Lex.Lex{Lex.Idle{}, [], []}

# the parser's start
def pp0() -> Parse.P:
  Parse.P{False{}, None{}, []}

# the tokens a lexer state stands for, reversed, its open word pushed
def eff(lx: Lex.Lex) -> List<&2, Lex.Tok>:
  match lx:
    case Lex.Lex{Lex.Word{}, buf, toks}:
      Lex.TWord{Lex.text(buf)} <> toks
    case Lex.Lex{_, _, toks}:
      toks

# the parser after a lexer state's tokens, spans read out
def pst(lx: Lex.Lex) -> Parse.P:
  Parse.run(dens(List.reverse(&2, Lex.Tok, eff(lx))), pp0())

# a lexer state between tokens: idle, or in a word that the next character ends
def cm(lx: Lex.Lex, +x: String) -> Bool:
  match lx:
    case Lex.Lex{Lex.Idle{}, _, _}:
      True{}
    case Lex.Lex{Lex.Word{}, _, _}:
      stops(x)
    case _:
      False{}

# no cells
def jnil(val: V.Json) -> Bool:
  match val:
    case V.JNil{}:
      True{}
    case _:
      False{}

# an array frame's slot of the cursor and of the parser in the same place
def sl.a(ps: Pull.Slot, fr: Bool, items: V.Json, qs: Parse.Slot) -> Bool:
  match ps qs:
    case Pull.SVal{} Parse.SValue{}:
      Bool.or(Bool.not(fr), jnil(items))
    case Pull.SCom{} Parse.SComma{}:
      True{}
    case _ _:
      False{}

# an object frame's slot of the cursor and of the parser in the same place
def sl.o(ps: Pull.Slot, fr: Bool, pairs: V.Json, qs: Parse.Slot) -> Bool:
  match ps qs:
    case Pull.SKey{} Parse.SKey{}:
      Bool.or(Bool.not(fr), jnil(pairs))
    case Pull.SCol{} Parse.SColon{}:
      True{}
    case Pull.SVal{} Parse.SValue{}:
      True{}
    case Pull.SCom{} Parse.SComma{}:
      True{}
    case _ _:
      False{}

# a cursor's array frame and a parser frame in the same place
def frel.a(ps: Pull.Slot, fr: Bool, qf: Parse.Frame) -> Bool:
  match qf:
    case Parse.FArr{items, qs}:
      sl.a(ps, fr, items, qs)
    case Parse.FObj{_, _, _}:
      False{}

# a cursor's object frame and a parser frame in the same place
def frel.o(ps: Pull.Slot, fr: Bool, qf: Parse.Frame) -> Bool:
  match qf:
    case Parse.FObj{pairs, _, qs}:
      sl.o(ps, fr, pairs, qs)
    case Parse.FArr{_, _}:
      False{}

# an open frame of the cursor and one of the parser in the same place: the
# same kind and slot, and no cells yet when the cursor's frame is fresh
def frel(pf: Pull.Frame, qf: Parse.Frame) -> Bool:
  match pf:
    case Pull.FArr{ps, fr}:
      frel.a(ps, fr, qf)
    case Pull.FObj{ps, fr}:
      frel.o(ps, fr, qf)

# every open frame in the same place
def frels(ps: List<&2, Pull.Frame>, qs: List<&2, Parse.Frame>) -> Bool:
  match ps qs:
    case Nil{} Nil{}:
      True{}
    case Con{pf, pt} Con{qf, qt}:
      Bool.and(frel(pf, qf), frels(pt, qt))
    case _ _:
      False{}

# the root: open while the cursor's is, finished (with no frame open) once it is
def rrel(done: Bool, root: Maybe<&2, V.Json>, ps: List<&2, Pull.Frame>) -> Bool:
  match done root ps:
    case False{} None{} _:
      True{}
    case True{} Some{_} Nil{}:
      True{}
    case _ _ _:
      False{}

# the cursor's frames and root and a parser that has not failed, in the same place
def prel(+ps: List<&2, Pull.Frame>, done: Bool, pp: Parse.P) -> Bool:
  match pp:
    case Parse.P{False{}, root, qs}:
      Bool.and(rrel(done, root, ps), frels(ps, qs))
    case Parse.P{True{}, _, _}:
      False{}

# the lexer on the whole text is the lexer state lx on what is left
def lx_e(t: String, x: String, lx: Lex.Lex) -> Data:
  {Lex.run(String.to_list(t), lx0()) == Lex.run(String.to_list(x), lx) : Lex.Lex}

# a live cursor between tokens, in step with the lexer and the parser
def cinv(t: String, cur: Pull.Cur) -> Type:
  match cur:
    case Pull.Cur{+rest, +stack, +done, False{}}:
      ({D1.short(rest) == True{} : Bool} & (&lx: Lex.Lex -> (lx_e(t, rest, lx) & ({cm(lx, rest) == True{} : Bool}
        & {prel(stack, done, pst(lx)) == True{} : Bool}))))
    case Pull.Cur{_, _, _, True{}}:
      Empty

# what one call of next leaves: a failed cursor, the end of a text that
# parses, or another event on a cursor in step
def post(tt: String, rr: (Pull.Ev & Pull.Cur)) -> Type:
  match rr:
    case (Pull.EErr{}, cur):
      {cur == Pull.Cur{"", [], False{}, True{}} : Pull.Cur}
    case (Pull.EEnd{}, _):
      {D1.is_some(Ezjson.parse(tt)) == True{} : Bool}
    case (_, cur):
      cinv(tt, cur)
