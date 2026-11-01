# the error token: tokens that hold it do not parse
import Base
import ../../src/value.bend as V
import ../../main.bend as Ezjson
import ../../src/lex.bend as Lex
import ../../src/parse.bend as Parse
import ../../laws/defs/CursorAndNumberRules.bend as D1
import ./ArrayLength.bend as M1
import ./CharacterClasses.bend as M2
import ./LexemeOrder.bend as M3
import ./LexerErrorSticks.bend as M4
import ./OwnedParse.bend as M5
import ./WellFormedCells.bend as M6

# a character whose class is not a quote is not U+0022
law nq:
  for bb: Bool
  for +uu: U32
  for cls: Lex.Class
  for eb: {U32.is_eq(uu, 34) == bb : Bool}
  for ecls: {Lex.classify(Chr{uu}) == cls : Lex.Class}
  for hq: {M2.is_quote(cls) == False{} : Bool}
  {U32.is_eq(uu, 34) == False{} : Bool}

def nq(bb, uu, cls, eb, ecls, hq):
  match bb:
    case False{}:
      eb
    case True{}:
      Empty.absurd({U32.is_eq(uu, 34) == False{} : Bool}, M1.true_false(Equal.trans(Bool, True{},
        M2.is_quote(Lex.classify(Chr{uu})), False{},
        Equal.sym(Bool, M2.is_quote(Lex.classify(Chr{uu})), True{}, Equal.cong(U32, Bool,
          zz => M2.is_quote(Lex.classify(Chr{zz})),
          uu, 34, M6.ueq(uu, 34, eb))),
        Equal.trans(Bool, M2.is_quote(Lex.classify(Chr{uu})), M2.is_quote(cls), False{},
          Equal.cong(Lex.Class, Bool, zz => M2.is_quote(zz), Lex.classify(Chr{uu}), cls, ecls), hq))))

# a character whose class is not a backslash is not U+005C
law nb:
  for bb: Bool
  for +uu: U32
  for cls: Lex.Class
  for eb: {U32.is_eq(uu, 92) == bb : Bool}
  for ecls: {Lex.classify(Chr{uu}) == cls : Lex.Class}
  for hb: {M2.is_back(cls) == False{} : Bool}
  {U32.is_eq(uu, 92) == False{} : Bool}

def nb(bb, uu, cls, eb, ecls, hb):
  match bb:
    case False{}:
      eb
    case True{}:
      Empty.absurd({U32.is_eq(uu, 92) == False{} : Bool}, M1.true_false(Equal.trans(Bool, True{},
        M2.is_back(Lex.classify(Chr{uu})), False{},
        Equal.sym(Bool, M2.is_back(Lex.classify(Chr{uu})), True{}, Equal.cong(U32, Bool,
          zz => M2.is_back(Lex.classify(Chr{zz})),
          uu, 92, M6.ueq(uu, 92, eb))),
        Equal.trans(Bool, M2.is_back(Lex.classify(Chr{uu})), M2.is_back(cls), False{},
          Equal.cong(Lex.Class, Bool, zz => M2.is_back(zz), Lex.classify(Chr{uu}), cls, ecls), hb))))

# whether a token is the error token
def is_tbad(tok: Lex.Tok) -> Bool:
  match tok:
    case Lex.TBad{}:
      True{}
    case _:
      False{}

# whether a token list holds the error token
def has_bad(xs: List<&2, Lex.Tok>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case hd <> tl:
      Bool.or(is_tbad(hd), has_bad(tl))

# an or with a true right side
law or_true_r:
  for aa: Bool
  {Bool.or(aa, True{}) == True{} : Bool}

def or_true_r(aa):
  match aa:
    case True{}:
      {==}
    case False{}:
      {==}

# the error token, reversed onto tokens, stays
law hb_rev:
  for +xs: List<&2, Lex.Tok>
  for +acc: List<&2, Lex.Tok>
  for h: {has_bad(acc) == True{} : Bool}
  {has_bad(List.reverse.go(&2, Lex.Tok, xs, acc)) == True{} : Bool}

def hb_rev(xs, acc, h):
  match xs:
    case Nil{}:
      h
    case +hd <> +tl:
      hb_rev(tl, hd <> acc, Equal.trans(Bool, Bool.or(is_tbad(hd), has_bad(acc)), Bool.or(is_tbad(hd), True{}), True{},
        Equal.cong(Bool, Bool, zz => Bool.or(is_tbad(hd), zz), has_bad(acc), True{}, h), or_true_r(is_tbad(hd))))

# reading spans out keeps the error token
law hb_dens:
  for +xs: List<&2, Lex.Tok>
  {has_bad(M3.dens(xs)) == has_bad(xs) : Bool}

def hb_dens(xs):
  match xs:
    case Nil{}:
      {==}
    case hd <> +tl:
      match hd:
        case Lex.TOpenArr{}:
          Equal.cong(Bool, Bool, zz => Bool.or(is_tbad(Lex.TOpenArr{}), zz), has_bad(M3.dens(tl)), has_bad(tl),
            hb_dens(tl))
        case Lex.TCloseArr{}:
          Equal.cong(Bool, Bool, zz => Bool.or(is_tbad(Lex.TCloseArr{}), zz), has_bad(M3.dens(tl)), has_bad(tl),
            hb_dens(tl))
        case Lex.TOpenObj{}:
          Equal.cong(Bool, Bool, zz => Bool.or(is_tbad(Lex.TOpenObj{}), zz), has_bad(M3.dens(tl)), has_bad(tl),
            hb_dens(tl))
        case Lex.TCloseObj{}:
          Equal.cong(Bool, Bool, zz => Bool.or(is_tbad(Lex.TCloseObj{}), zz), has_bad(M3.dens(tl)), has_bad(tl),
            hb_dens(tl))
        case Lex.TColon{}:
          Equal.cong(Bool, Bool, zz => Bool.or(is_tbad(Lex.TColon{}), zz), has_bad(M3.dens(tl)), has_bad(tl),
              hb_dens(tl))
        case Lex.TComma{}:
          Equal.cong(Bool, Bool, zz => Bool.or(is_tbad(Lex.TComma{}), zz), has_bad(M3.dens(tl)), has_bad(tl),
              hb_dens(tl))
        case Lex.TStr{+t1}:
          Equal.cong(Bool, Bool, zz => Bool.or(is_tbad(Lex.TStr{t1}), zz), has_bad(M3.dens(tl)), has_bad(tl),
              hb_dens(tl))
        case Lex.TWord{+t1}:
          Equal.cong(Bool, Bool, zz => Bool.or(is_tbad(Lex.TWord{t1}), zz), has_bad(M3.dens(tl)), has_bad(tl),
              hb_dens(tl))
        case Lex.TStrS{+t1, +t2}:
          Equal.cong(Bool, Bool, zz => Bool.or(is_tbad(Lex.TStrS{t1, t2}), zz), has_bad(M3.dens(tl)), has_bad(tl),
            hb_dens(tl))
        case Lex.TWordS{+t1, +t2}:
          Equal.cong(Bool, Bool, zz => Bool.or(is_tbad(Lex.TWordS{t1, t2}), zz), has_bad(M3.dens(tl)), has_bad(tl),
            hb_dens(tl))
        case Lex.TBad{}:
          Equal.cong(Bool, Bool, zz => Bool.or(is_tbad(Lex.TBad{}), zz), has_bad(M3.dens(tl)), has_bad(tl), hb_dens(tl))

# the error token raises the error flag
law tbad_bad:
  for st: Parse.P
  {M4.pbad(Parse.step(Lex.TBad{}, st)) == True{} : Bool}

def tbad_bad(st):
  match st:
    case Parse.P{_bad, _root, _stk}:
      {==}

# tokens that hold the error token do not parse
law bad_none:
  for xs: List<&2, Lex.Tok>
  for +st: Parse.P
  for h: {has_bad(xs) == True{} : Bool}
  {Parse.finish(Parse.run(xs, st)) == None{} : Maybe<&2, V.Json>}

def bad_none(xs, st, h):
  match xs:
    case Nil{}:
      M3.no({Parse.finish(st) == None{} : Maybe<&2, V.Json>}, h)
    case hd <> +tl:
      match hd:
        case Lex.TOpenArr{}:
          bad_none(tl, Parse.step(Lex.TOpenArr{}, st), h)
        case Lex.TCloseArr{}:
          bad_none(tl, Parse.step(Lex.TCloseArr{}, st), h)
        case Lex.TOpenObj{}:
          bad_none(tl, Parse.step(Lex.TOpenObj{}, st), h)
        case Lex.TCloseObj{}:
          bad_none(tl, Parse.step(Lex.TCloseObj{}, st), h)
        case Lex.TColon{}:
          bad_none(tl, Parse.step(Lex.TColon{}, st), h)
        case Lex.TComma{}:
          bad_none(tl, Parse.step(Lex.TComma{}, st), h)
        case Lex.TStr{+t1}:
          bad_none(tl, Parse.step(Lex.TStr{t1}, st), h)
        case Lex.TWord{+t1}:
          bad_none(tl, Parse.step(Lex.TWord{t1}, st), h)
        case Lex.TStrS{+t1, +t2}:
          bad_none(tl, Parse.step(Lex.TStrS{t1, t2}, st), h)
        case Lex.TWordS{+t1, +t2}:
          bad_none(tl, Parse.step(Lex.TWordS{t1, t2}, st), h)
        case Lex.TBad{}:
          M4.fin_bad(Parse.run(tl, Parse.step(Lex.TBad{}, st)), M4.run_bad(tl, Parse.step(Lex.TBad{}, st),
              tbad_bad(st)))

# laws/EscapesDecode.bend: \u escapes that make parse None

# a lexer state whose tokens hold the error token
def rj(lx: Lex.Lex) -> Type:
  {has_bad(Lex.finish(lx)) == True{} : Bool}

# a text whose character lexer rejects it does not parse
law lex_none:
  for +txt: String
  for h_s: {D1.short(txt) == True{} : Bool}
  for h: rj(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))
  {Ezjson.parse(txt) == None{} : Maybe<&2, V.Json>}

def lex_none(txt, h_s, h):
  M4.own_m_none(Ezjson.parse(txt), Equal.trans(Maybe<&2, V.Json>, D1.own_m(Parse.finish(Parse.run(Lex.tokens(txt),
    Parse.P{False{}, None{}, Nil{}}))), Parse.finish(M5.ownp(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{},
    Nil{}}))), None{}, M5.fin_own(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}})), Equal.trans(Maybe<&2,
    V.Json>, Parse.finish(M5.ownp(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}}))),
    Parse.finish(Parse.run(M3.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}})), None{}, Equal.cong(Parse.P,
    Maybe<&2, V.Json>, zz => Parse.finish(zz), M5.ownp(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}})),
    Parse.run(M3.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}}), M5.run_own(Lex.tokens(txt), Parse.P{False{},
    None{}, Nil{}})), Equal.trans(Maybe<&2, V.Json>, Parse.finish(Parse.run(M3.dens(Lex.tokens(txt)), Parse.P{False{},
    None{}, Nil{}})), Parse.finish(Parse.run(M3.dens(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [],
    []}))), Parse.P{False{}, None{}, Nil{}})), None{}, Equal.cong(List<&2, Lex.Tok>, Maybe<&2, V.Json>,
    zz => Parse.finish(Parse.run(zz, Parse.P{False{}, None{}, Nil{}})), M3.dens(Lex.tokens(txt)),
    M3.dens(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))), M2.lexers_agree(txt, h_s)),
    bad_none(M3.dens(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))), Parse.P{False{}, None{},
    Nil{}}, Equal.trans(Bool, has_bad(M3.dens(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []})))),
    has_bad(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))), True{},
    hb_dens(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))), h))))))
