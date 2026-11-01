# string tokens: raw characters and one string parsed
import Base
import ../../src/value.bend as V
import ../../src/lex.bend as Lex
import ../../src/parse.bend as Parse
import ../../laws/defs/CursorAndNumberRules.bend as D1
import ./ArrayLength.bend as M1
import ./CharacterClasses.bend as M2
import ./LexemeOrder.bend as M3

# a string character that is none of `"`, `\` and the controls stays itself
law str_other:
  for cls: Lex.Class
  for +uu: U32
  for ecls: {Lex.classify(Chr{uu}) == cls : Lex.Class}
  for e34: {U32.is_eq(uu, 34) == False{} : Bool}
  for e92: {U32.is_eq(uu, 92) == False{} : Bool}
  for ect: {U32.is_lt(uu, 32) == False{} : Bool}
  for buf: List<&2, Char>
  for toks: List<&2, Lex.Tok>
  {Lex.step(Lex.Str{}, cls, Chr{uu}, buf, toks) == Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks} : Lex.Lex}

def str_other(cls, uu, ecls, e34, e92, ect, buf, toks):
  match cls:
    case Lex.CQuote{}:
      Empty.absurd({Lex.step(Lex.Str{}, Lex.CQuote{}, Chr{uu}, buf, toks) == Lex.Lex{Lex.Str{}, Chr{uu} <> buf,
        toks} : Lex.Lex},
        M3.false_true(Equal.trans(Bool, False{}, U32.is_eq(uu, 34), True{}, Equal.sym(Bool, U32.is_eq(uu, 34), False{},
          e34),
          Equal.cong(U32, Bool, xx => U32.is_eq(xx, 34), uu, 34, M2.cls_quote(Chr{uu}, ecls)))))
    case Lex.CBack{}:
      Empty.absurd({Lex.step(Lex.Str{}, Lex.CBack{}, Chr{uu}, buf, toks) == Lex.Lex{Lex.Str{}, Chr{uu} <> buf,
        toks} : Lex.Lex},
        M3.false_true(Equal.trans(Bool, False{}, U32.is_eq(uu, 92), True{}, Equal.sym(Bool, U32.is_eq(uu, 92), False{},
          e92),
          Equal.cong(U32, Bool, xx => U32.is_eq(xx, 92), uu, 92, M2.cls_back(Chr{uu}, ecls)))))
    case Lex.CPunct{tt}:
      ec = Equal.sym(Bool, U32.is_lt(uu, 32), False{}, ect)
      %ec : {Lex.step.str.go(Chr{uu}, buf, toks, _) == Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks} : Lex.Lex}
      {==}
    case Lex.CSpace{}:
      ec = Equal.sym(Bool, U32.is_lt(uu, 32), False{}, ect)
      %ec : {Lex.step.str.go(Chr{uu}, buf, toks, _) == Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks} : Lex.Lex}
      {==}
    case Lex.COther{}:
      ec = Equal.sym(Bool, U32.is_lt(uu, 32), False{}, ect)
      %ec : {Lex.step.str.go(Chr{uu}, buf, toks, _) == Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks} : Lex.Lex}
      {==}

# the character lexer on two strings is the lexer on the first, then the second
law run_app:
  for +aa: String
  for +bb: String
  for st: Lex.Lex
  {Lex.run(String.to_list(aa ++ bb), st) == Lex.run(String.to_list(bb), Lex.run(String.to_list(aa), st)) : Lex.Lex}

def run_app(aa, bb, st):
  match aa:
    case SNil{}:
      {==}
    case SCon{+hd, +tl}:
      run_app(tl, bb, Lex.feed(hd, st))

# the lexer on two strings, where the first leads to a known state
law seq:
  for +aa: String
  for +bb: String
  for +st: Lex.Lex
  for +mid: Lex.Lex
  for e1: {Lex.run(String.to_list(aa), st) == mid : Lex.Lex}
  {Lex.run(String.to_list(aa ++ bb), st) == Lex.run(String.to_list(bb), mid) : Lex.Lex}

def seq(aa, bb, st, mid, e1):
  Equal.trans(Lex.Lex, Lex.run(String.to_list(aa ++ bb), st), Lex.run(String.to_list(bb), Lex.run(String.to_list(aa),
    st)),
    Lex.run(String.to_list(bb), mid), run_app(aa, bb, st),
    Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list(bb), xx), Lex.run(String.to_list(aa), st), mid, e1))

# whether a token is a string token
def is_tstr(tok: Lex.Tok) -> Bool:
  match tok:
    case Lex.TStr{_}:
      True{}
    case _:
      False{}

# a string token's text
def tstr_of(tok: Lex.Tok) -> String:
  match tok:
    case Lex.TStr{txt}:
      txt
    case _:
      ""

# a token that means a string parses, alone, as a string of its characters
law one_tok:
  for tok: Lex.Tok
  for +txt: String
  for eh: {M3.den(tok) == Lex.TStr{txt} : Lex.Tok}
  {D1.str_of(Parse.finish(Parse.run([tok], Parse.P{False{}, None{}, Nil{}}))) == Some{txt} : Maybe<&2, String>}

def one_tok(tok, txt, eh):
  match tok:
    case Lex.TStr{+yy}:
      Equal.cong(String, Maybe<&2, String>, xx => Some{xx}, yy, txt,
        Equal.cong(Lex.Tok, String, xx => tstr_of(xx), Lex.TStr{yy}, Lex.TStr{txt}, eh))
    case Lex.TStrS{+src, +nn}:
      Equal.cong(String, Maybe<&2, String>, xx => Some{xx}, V.span.str(src, nn, U32.is_zero(nn)), txt,
        Equal.cong(Lex.Tok, String, xx => tstr_of(xx), Lex.TStr{V.span.str(src, nn, U32.is_zero(nn))}, Lex.TStr{txt},
          eh))
    case Lex.TOpenArr{}:
      Empty.absurd({D1.str_of(Parse.finish(Parse.run([Lex.TOpenArr{}], Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, M3.false_true(Equal.cong(Lex.Tok, Bool, xx => is_tstr(xx), Lex.TOpenArr{},
          Lex.TStr{txt}, eh)))
    case Lex.TCloseArr{}:
      Empty.absurd({D1.str_of(Parse.finish(Parse.run([Lex.TCloseArr{}], Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, M3.false_true(Equal.cong(Lex.Tok, Bool, xx => is_tstr(xx), Lex.TCloseArr{},
          Lex.TStr{txt}, eh)))
    case Lex.TOpenObj{}:
      Empty.absurd({D1.str_of(Parse.finish(Parse.run([Lex.TOpenObj{}], Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, M3.false_true(Equal.cong(Lex.Tok, Bool, xx => is_tstr(xx), Lex.TOpenObj{},
          Lex.TStr{txt}, eh)))
    case Lex.TCloseObj{}:
      Empty.absurd({D1.str_of(Parse.finish(Parse.run([Lex.TCloseObj{}], Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, M3.false_true(Equal.cong(Lex.Tok, Bool, xx => is_tstr(xx), Lex.TCloseObj{},
          Lex.TStr{txt}, eh)))
    case Lex.TColon{}:
      Empty.absurd({D1.str_of(Parse.finish(Parse.run([Lex.TColon{}], Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, M3.false_true(Equal.cong(Lex.Tok, Bool, xx => is_tstr(xx), Lex.TColon{},
          Lex.TStr{txt}, eh)))
    case Lex.TComma{}:
      Empty.absurd({D1.str_of(Parse.finish(Parse.run([Lex.TComma{}], Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, M3.false_true(Equal.cong(Lex.Tok, Bool, xx => is_tstr(xx), Lex.TComma{},
          Lex.TStr{txt}, eh)))
    case Lex.TWord{+raw}:
      Empty.absurd({D1.str_of(Parse.finish(Parse.run([Lex.TWord{raw}], Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, M3.false_true(Equal.cong(Lex.Tok, Bool, xx => is_tstr(xx), Lex.TWord{raw},
          Lex.TStr{txt}, eh)))
    case Lex.TWordS{+src, +nn}:
      Empty.absurd({D1.str_of(Parse.finish(Parse.run([Lex.TWordS{src, nn}], Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, M3.false_true(Equal.cong(Lex.Tok, Bool, xx => is_tstr(xx),
          Lex.TWord{V.span.str(src, nn, U32.is_zero(nn))}, Lex.TStr{txt}, eh)))
    case Lex.TBad{}:
      Empty.absurd({D1.str_of(Parse.finish(Parse.run([Lex.TBad{}], Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, M3.false_true(Equal.cong(Lex.Tok, Bool, xx => is_tstr(xx), Lex.TBad{},
          Lex.TStr{txt}, eh)))

# one_str, once the list is split
law one_str.at:
  for rest: List<&2, Lex.Tok>
  for tok: Lex.Tok
  for +txt: String
  for eh: {M3.den(tok) == Lex.TStr{txt} : Lex.Tok}
  for er: {M3.dens(rest) == [] : List<&2, Lex.Tok>}
  {D1.str_of(Parse.finish(Parse.run(tok <> rest, Parse.P{False{}, None{}, Nil{}}))) == Some{txt} :
    Maybe<&2, String>}

def one_str.at(rest, tok, txt, eh, er):
  match rest:
    case Nil{}:
      one_tok(tok, txt, eh)
    case r1 <> r2:
      Empty.absurd({D1.str_of(Parse.finish(Parse.run(tok <> r1 <> r2, Parse.P{False{}, None{}, Nil{}}))) ==
        Some{txt} : Maybe<&2, String>}, M3.false_true(Equal.cong(List<&2, Lex.Tok>, Bool, xx => M2.tnil(xx),
          M3.den(r1) <> M3.dens(r2), [], er)))

# tokens that mean one string token parse as a string of its characters
law one_str:
  for xs: List<&2, Lex.Tok>
  for +txt: String
  for +ex: {M3.dens(xs) == [Lex.TStr{txt}] : List<&2, Lex.Tok>}
  {D1.str_of(Parse.finish(Parse.run(xs, Parse.P{False{}, None{}, Nil{}}))) == Some{txt} : Maybe<&2, String>}

def one_str(xs, txt, ex):
  match xs:
    case Nil{}:
      Empty.absurd({D1.str_of(Parse.finish(Parse.run([], Parse.P{False{}, None{}, Nil{}}))) == Some{txt} :
        Maybe<&2, String>}, M1.true_false(Equal.cong(List<&2, Lex.Tok>, Bool, yy => M2.tnil(yy), [], [Lex.TStr{txt}],
            ex)))
    case +hd <> +tl:
      one_str.at(tl, hd, txt,
        Equal.cong(List<&2, Lex.Tok>, Lex.Tok, yy => M2.thead(yy), M3.den(hd) <> M3.dens(tl), [Lex.TStr{txt}], ex),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => M2.ttail(yy), M3.den(hd) <> M3.dens(tl),
            [Lex.TStr{txt}], ex))

# laws/RawControlCharsRefused.bend: raw characters in strings

# a false or
law or_false_l:
  for aa: Bool
  for -bb: Bool
  for h: {Bool.or(aa, bb) == False{} : Bool}
  {aa == False{} : Bool}

def or_false_l(aa, _bb, h):
  match aa:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, M1.true_false(h))
    case False{}:
      {==}

# a false or, the right side
law or_false_r:
  for aa: Bool
  for -bb: Bool
  for h: {Bool.or(aa, bb) == False{} : Bool}
  {bb == False{} : Bool}

def or_false_r(aa, _bb, h):
  match aa:
    case True{}:
      Empty.absurd({_bb == False{} : Bool}, M1.true_false(h))
    case False{}:
      h

# a true not
law not_true:
  for bb: Bool
  for h: {Bool.not(bb) == True{} : Bool}
  {bb == False{} : Bool}

def not_true(bb, h):
  match bb:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, M3.false_true(h))
    case False{}:
      {==}

# raw characters a string keeps, read inside the string
law lex_raw:
  for +cs: List<&2, Char>
  for +h: {D1.raw_ok(cs) == True{} : Bool}
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {Lex.run(cs, Lex.Lex{Lex.Str{}, buf, toks}) == Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, cs, buf), toks} : Lex.Lex}

def lex_raw(cs, h, buf, toks):
  match cs:
    case Nil{}:
      {==}
    case Chr{+uu} <> +tl:
      +ab = Bool.or(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_lt(uu, 32)))
      +hc = M3.and_left(D1.raw_char(Chr{uu}), D1.raw_ok(tl), h)
      +hn = not_true(ab, hc)
      +hr = or_false_r(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_lt(uu, 32)), hn)
      e34 = or_false_l(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_lt(uu, 32)), hn)
      e92 = or_false_l(U32.is_eq(uu, 92), U32.is_lt(uu, 32), hr)
      ect = or_false_r(U32.is_eq(uu, 92), U32.is_lt(uu, 32), hr)
      Equal.trans(Lex.Lex, Lex.run(tl, Lex.feed(Chr{uu}, Lex.Lex{Lex.Str{}, buf, toks})),
        Lex.run(tl, Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks}), Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, tl,
          Chr{uu} <> buf), toks},
        Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(tl, zz), Lex.feed(Chr{uu}, Lex.Lex{Lex.Str{}, buf, toks}),
          Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks},
          Equal.trans(Lex.Lex, Lex.feed(Chr{uu}, Lex.Lex{Lex.Str{}, buf, toks}),
            Lex.step(Lex.Str{}, Lex.classify(Chr{uu}), Chr{uu}, buf, toks), Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks},
            M3.feed_as(Chr{uu}, Lex.Str{}, buf, toks, Lex.classify(Chr{uu}), {==}),
            str_other(Lex.classify(Chr{uu}), uu, {==}, e34, e92, ect, buf, toks))),
        lex_raw(tl, M3.and_right(D1.raw_char(Chr{uu}), D1.raw_ok(tl), h), Chr{uu} <> buf, toks))
