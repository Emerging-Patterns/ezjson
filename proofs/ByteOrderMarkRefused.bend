# proofs of laws/ByteOrderMarkRefused.bend
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../src/lex.bend as Lex
import ../src/parse.bend as Parse
import ../laws/ByteOrderMarkRefused.bend as Laws
import ../laws/defs/CursorAndNumberRules.bend as D1
import ./lemmas/ArrayLength.bend as M1
import ./lemmas/CharacterClasses.bend as M2
import ./lemmas/LexemeOrder.bend as M3
import ./lemmas/LexerErrorSticks.bend as M4
import ./lemmas/NumOkStates.bend as M5
import ./lemmas/OwnedParse.bend as M6
import ./lemmas/WellFormedCells.bend as M7

# a token put at the bottom comes out first
law fin_head:
  for lx: Lex.Lex
  for +t0: Lex.Tok
  {M2.thead(Lex.finish(M2.lex.app(lx, [t0]))) == t0 : Lex.Tok}

def fin_head(lx, t0):
  match lx:
    case Lex.Lex{md, +bf, +tk}:
      match md:
        case Lex.Idle{}:
          Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz), List.reverse.go(&2, Lex.Tok, List.append(&2,
              Lex.Tok,
            tk, [t0]), Nil{}), List.reverse.go(&2, Lex.Tok, [t0], List.reverse.go(&2, Lex.Tok, tk, Nil{})),
            M7.rev_app(tk, [t0], Nil{}))
        case Lex.Word{}:
          Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz), List.reverse.go(&2, Lex.Tok, List.append(&2,
              Lex.Tok,
            tk, [t0]), [Lex.TWord{Lex.text(bf)}]), List.reverse.go(&2, Lex.Tok, [t0], List.reverse.go(&2, Lex.Tok, tk,
            [Lex.TWord{Lex.text(bf)}])),
            M7.rev_app(tk, [t0], [Lex.TWord{Lex.text(bf)}]))
        case Lex.Str{}:
          Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz), List.reverse.go(&2, Lex.Tok, List.append(&2,
              Lex.Tok,
            tk, [t0]), [Lex.TBad{}]), List.reverse.go(&2, Lex.Tok, [t0], List.reverse.go(&2, Lex.Tok, tk,
            [Lex.TBad{}])),
            M7.rev_app(tk, [t0], [Lex.TBad{}]))
        case Lex.Esc{}:
          Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz), List.reverse.go(&2, Lex.Tok, List.append(&2,
              Lex.Tok,
            tk, [t0]), [Lex.TBad{}]), List.reverse.go(&2, Lex.Tok, [t0], List.reverse.go(&2, Lex.Tok, tk,
            [Lex.TBad{}])),
            M7.rev_app(tk, [t0], [Lex.TBad{}]))
        case Lex.Uni{+l1, +a1}:
          Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz), List.reverse.go(&2, Lex.Tok, List.append(&2,
              Lex.Tok,
            tk, [t0]), [Lex.TBad{}]), List.reverse.go(&2, Lex.Tok, [t0], List.reverse.go(&2, Lex.Tok, tk,
            [Lex.TBad{}])),
            M7.rev_app(tk, [t0], [Lex.TBad{}]))
        case Lex.Hi{+h1}:
          Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz), List.reverse.go(&2, Lex.Tok, List.append(&2,
              Lex.Tok,
            tk, [t0]), [Lex.TBad{}]), List.reverse.go(&2, Lex.Tok, [t0], List.reverse.go(&2, Lex.Tok, tk,
            [Lex.TBad{}])),
            M7.rev_app(tk, [t0], [Lex.TBad{}]))
        case Lex.HiEsc{+h1}:
          Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz), List.reverse.go(&2, Lex.Tok, List.append(&2,
              Lex.Tok,
            tk, [t0]), [Lex.TBad{}]), List.reverse.go(&2, Lex.Tok, [t0], List.reverse.go(&2, Lex.Tok, tk,
            [Lex.TBad{}])),
            M7.rev_app(tk, [t0], [Lex.TBad{}]))
        case Lex.Lo{+l1, +a1, +h1}:
          Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz), List.reverse.go(&2, Lex.Tok, List.append(&2,
              Lex.Tok,
            tk, [t0]), [Lex.TBad{}]), List.reverse.go(&2, Lex.Tok, [t0], List.reverse.go(&2, Lex.Tok, tk,
            [Lex.TBad{}])),
            M7.rev_app(tk, [t0], [Lex.TBad{}]))
        case Lex.Bad{}:
          Equal.cong(List<&2, Lex.Tok>, Lex.Tok, zz => M2.thead(zz), List.reverse.go(&2, Lex.Tok, List.append(&2,
              Lex.Tok,
            tk, [t0]), [Lex.TBad{}]), List.reverse.go(&2, Lex.Tok, [t0], List.reverse.go(&2, Lex.Tok, tk,
            [Lex.TBad{}])),
            M7.rev_app(tk, [t0], [Lex.TBad{}]))

# a character on top of a reversed prefix
law rev_snoc:
  for +pre: List<&2, Char>
  for +ch: Char
  for +acc: List<&2, Char>
  {List.reverse.go(&2, Char, List.append(&2, Char, pre, [ch]), acc) == ch <> List.reverse.go(&2, Char, pre,
    acc) : List<&2, Char>}

def rev_snoc(pre, ch, acc):
  match pre:
    case Nil{}:
      {==}
    case +hd <> +tl:
      rev_snoc(tl, ch, hd <> acc)

# whether the parser, from the start, raises its error flag on a token
def wrej(tok: Lex.Tok) -> Bool:
  M4.pbad(Parse.step(tok, Parse.P{False{}, None{}, Nil{}}))

# tokens whose first one raises the error flag do not parse
law rej_none:
  for xs: List<&2, Lex.Tok>
  for h: {wrej(M2.thead(xs)) == True{} : Bool}
  {Parse.finish(Parse.run(xs, Parse.P{False{}, None{}, Nil{}})) == None{} : Maybe<&2, V.Json>}

def rej_none(xs, h):
  match xs:
    case Nil{}:
      {==}
    case +tok <> +rest:
      M4.fin_bad(Parse.run(rest, Parse.step(tok, Parse.P{False{}, None{}, Nil{}})), M4.run_bad(rest, Parse.step(tok,
        Parse.P{False{}, None{}, Nil{}}), h))

# the first token, with spans read out
law dens_head:
  for xs: List<&2, Lex.Tok>
  {M2.thead(M3.dens(xs)) == M3.den(M2.thead(xs)) : Lex.Tok}

def dens_head(xs):
  match xs:
    case Nil{}:
      {==}
    case _hd <> _tl:
      {==}

# a word that starts with U+FEFF is rejected
law feff_word:
  for +txt: String
  {wrej(Lex.TWord{SCon{Chr{65279}, txt}}) == True{} : Bool}

def feff_word(txt):
  # U+FEFF is above every literal's first letter, so String.eq walks the
  # rest already GT and answers False
  n1 = Equal.sym(Bool, Cmp.is_eq(String.order.go(txt, "ull", GT{})), False{}, M1.order_go_ne_eq(txt, "ull", GT{}, {==}))
  %n1 : {M4.pbad(Parse.step.word.go(SCon{Chr{65279}, txt}, Parse.P{False{}, None{}, Nil{}},
    Bool.or(_, Bool.or(Cmp.is_eq(String.order.go(txt, "rue", GT{})),
      Bool.or(Cmp.is_eq(String.order.go(txt, "alse", GT{})), V.num.ok.go(String.to_list(txt), V.NBad{})))))) ==
    True{} : Bool}
  n2 = Equal.sym(Bool, Cmp.is_eq(String.order.go(txt, "rue", GT{})), False{}, M1.order_go_ne_eq(txt, "rue", GT{}, {==}))
  %n2 : {M4.pbad(Parse.step.word.go(SCon{Chr{65279}, txt}, Parse.P{False{}, None{}, Nil{}},
    Bool.or(_, Bool.or(Cmp.is_eq(String.order.go(txt, "alse", GT{})), V.num.ok.go(String.to_list(txt), V.NBad{}))))) ==
    True{} : Bool}
  n3 = Equal.sym(Bool, Cmp.is_eq(String.order.go(txt, "alse", GT{})), False{}, M1.order_go_ne_eq(txt, "alse", GT{},
      {==}))
  %n3 : {M4.pbad(Parse.step.word.go(SCon{Chr{65279}, txt}, Parse.P{False{}, None{}, Nil{}},
    Bool.or(_, V.num.ok.go(String.to_list(txt), V.NBad{})))) == True{} : Bool}
  sb = Equal.sym(Bool, V.num.ok.go(String.to_list(txt), V.NBad{}), False{}, M5.st_bad(String.to_list(txt)))
  %sb : {M4.pbad(Parse.step.word.go(SCon{Chr{65279}, txt}, Parse.P{False{}, None{}, Nil{}}, _)) == True{} : Bool}
  {==}

# what bom_go says: after U+FEFF and more word characters, the first token is rejected
def bomg(cs: List<&2, Char>, pre: List<&2, Char>) -> Type:
  {wrej(M3.den(M2.thead(Lex.finish(Lex.run(cs, Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, pre, [Chr{65279}]),
      []}))))) ==
    True{} : Bool}

# the word that starts with U+FEFF is rejected
law tw_rej:
  for +pre: List<&2, Char>
  {wrej(Lex.TWord{Lex.text(List.reverse.go(&2, Char, pre, [Chr{65279}]))}) == True{} : Bool}

def tw_rej(pre):
  Equal.trans(Bool, wrej(Lex.TWord{Lex.text(List.reverse.go(&2, Char, pre, [Chr{65279}]))}),
    wrej(Lex.TWord{SCon{Chr{65279}, String.from_list(pre) ++ ""}}), True{},
    Equal.cong(String, Bool, zz => wrej(Lex.TWord{zz}), Lex.text(List.reverse.go(&2, Char, pre, [Chr{65279}])),
      SCon{Chr{65279}, String.from_list(pre) ++ ""}, M3.text_revgo(pre, [Chr{65279}], "")),
    feff_word(String.from_list(pre) ++ ""))

# the word that starts with U+FEFF, as a token
def feff_tw(pre: List<&2, Char>) -> Lex.Tok:
  Lex.TWord{Lex.text(List.reverse.go(&2, Char, pre, [Chr{65279}]))}

# once the word is closed, it stays the first token
law rej_from:
  for +cs: List<&2, Char>
  for +l1: Lex.Lex
  for +pre: List<&2, Char>
  {wrej(M3.den(M2.thead(Lex.finish(Lex.run(cs, M2.lex.app(l1, [Lex.TWord{Lex.text(List.reverse.go(&2, Char, pre,
    [Chr{65279}]))}])))))) == True{} : Bool}

def rej_from(cs, l1, pre):
  +tw = feff_tw(pre)
  Equal.trans(Bool, wrej(M3.den(M2.thead(Lex.finish(Lex.run(cs, M2.lex.app(l1, [tw])))))), wrej(M3.den(tw)), True{},
    Equal.cong(Lex.Tok, Bool, zz => wrej(M3.den(zz)), M2.thead(Lex.finish(Lex.run(cs, M2.lex.app(l1, [tw])))), tw,
      Equal.trans(Lex.Tok, M2.thead(Lex.finish(Lex.run(cs, M2.lex.app(l1, [tw])))),
          M2.thead(Lex.finish(M2.lex.app(Lex.run(cs, l1),
        [tw]))), tw,
        Equal.cong(Lex.Lex, Lex.Tok, zz => M2.thead(Lex.finish(zz)), Lex.run(cs, M2.lex.app(l1, [tw])),
            M2.lex.app(Lex.run(cs,
          l1), [tw]), M6.run_pass(cs, l1, [tw])),
        fin_head(Lex.run(cs, l1), tw))),
    tw_rej(pre))

# bom_step, by the character's class
law bom_cls:
  for cls: Lex.Class
  for +ch: Char
  for +cs: List<&2, Char>
  for +pre: List<&2, Char>
  for ih: bomg(cs, List.append(&2, Char, pre, [ch]))
  {wrej(M3.den(M2.thead(Lex.finish(Lex.run(cs, Lex.step(Lex.Word{}, cls, ch, List.reverse.go(&2, Char, pre,
      [Chr{65279}]),
    [])))))) == True{} : Bool}

def bom_cls(cls, ch, cs, pre, ih):
  match cls:
    case Lex.COther{}:
      rs = rev_snoc(pre, ch, [Chr{65279}])
      %rs : {wrej(M3.den(M2.thead(Lex.finish(Lex.run(cs, Lex.Lex{Lex.Word{}, _, []}))))) == True{} : Bool}
      ih
    case Lex.CPunct{+pp}:
      rej_from(cs, Lex.Lex{Lex.Idle{}, [], [pp]}, pre)
    case Lex.CQuote{}:
      rej_from(cs, Lex.Lex{Lex.Str{}, [], []}, pre)
    case Lex.CSpace{}:
      rej_from(cs, Lex.Lex{Lex.Idle{}, [], []}, pre)
    case Lex.CBack{}:
      Equal.cong(Lex.Lex, Bool, zz => wrej(M3.den(M2.thead(Lex.finish(zz)))), Lex.run(cs, Lex.Lex{Lex.Bad{}, [], []}),
        Lex.Lex{Lex.Bad{}, [], []}, M4.bad_run(cs))

# bom_go, one character on, with its class named
law bom_step:
  for +cls: Lex.Class
  for +ch: Char
  for +cs: List<&2, Char>
  for +pre: List<&2, Char>
  for ecls: {Lex.classify(ch) == cls : Lex.Class}
  for ih: bomg(cs, List.append(&2, Char, pre, [ch]))
  bomg(ch <> cs, pre)

def bom_step(cls, ch, cs, pre, ecls, ih):
  +bf = List.reverse.go(&2, Char, pre, [Chr{65279}])
  fa = Equal.sym(Lex.Lex, Lex.feed(ch, Lex.Lex{Lex.Word{}, bf, []}), Lex.step(Lex.Word{}, cls, ch, bf, []),
    M3.feed_as(ch, Lex.Word{}, bf, [], cls, ecls))
  %fa : {wrej(M3.den(M2.thead(Lex.finish(Lex.run(cs, _))))) == True{} : Bool}
  bom_cls(cls, ch, cs, pre, ih)

# after U+FEFF, the first token is rejected
law bom_go:
  for +cs: List<&2, Char>
  for +pre: List<&2, Char>
  bomg(cs, pre)

def bom_go(cs, pre):
  match cs:
    case Nil{}:
      tw_rej(pre)
    case +hd <> +tl:
      bom_step(Lex.classify(hd), hd, tl, pre, {==}, bom_go(tl, List.append(&2, Char, pre, [hd])))

def Laws.bom_none(txt, h_s):
  M4.own_m_none(Ezjson.parse(SCon{Char.from_u32(65279), txt}),
    Equal.trans(Maybe<&2, V.Json>, D1.own_m(Parse.finish(Parse.run(Lex.tokens(SCon{Char.from_u32(65279), txt}),
      Parse.P{False{}, None{}, Nil{}}))), Parse.finish(M6.ownp(Parse.run(Lex.tokens(SCon{Char.from_u32(65279), txt}),
      Parse.P{False{}, None{}, Nil{}}))), None{}, M6.fin_own(Parse.run(Lex.tokens(SCon{Char.from_u32(65279), txt}),
      Parse.P{False{}, None{}, Nil{}})),
      Equal.trans(Maybe<&2, V.Json>, Parse.finish(M6.ownp(Parse.run(Lex.tokens(SCon{Char.from_u32(65279), txt}),
        Parse.P{False{}, None{}, Nil{}}))), Parse.finish(Parse.run(M3.dens(Lex.tokens(SCon{Char.from_u32(65279), txt})),
        Parse.P{False{}, None{}, Nil{}})), None{}, Equal.cong(Parse.P, Maybe<&2, V.Json>, zz => Parse.finish(zz),
        M6.ownp(Parse.run(Lex.tokens(SCon{Char.from_u32(65279), txt}), Parse.P{False{}, None{}, Nil{}})),
        Parse.run(M3.dens(Lex.tokens(SCon{Char.from_u32(65279), txt})), Parse.P{False{}, None{}, Nil{}}),
      M6.run_own(Lex.tokens(SCon{Char.from_u32(65279), txt}), Parse.P{False{}, None{}, Nil{}})),
      Equal.trans(Maybe<&2, V.Json>, Parse.finish(Parse.run(M3.dens(Lex.tokens(SCon{Char.from_u32(65279), txt})),
        Parse.P{False{}, None{}, Nil{}})),
        Parse.finish(Parse.run(M3.dens(Lex.finish(Lex.run(String.to_list(SCon{Char.from_u32(65279), txt}),
        Lex.Lex{Lex.Idle{}, [], []}))), Parse.P{False{}, None{}, Nil{}})), None{}, Equal.cong(List<&2, Lex.Tok>,
        Maybe<&2, V.Json>, zz => Parse.finish(Parse.run(zz, Parse.P{False{}, None{}, Nil{}})),
        M3.dens(Lex.tokens(SCon{Char.from_u32(65279), txt})),
        M3.dens(Lex.finish(Lex.run(String.to_list(SCon{Char.from_u32(65279), txt}), Lex.Lex{Lex.Idle{}, [], []}))),
        M2.lexers_agree(SCon{Char.from_u32(65279), txt}, h_s)),
      rej_none(M3.dens(Lex.finish(Lex.run(String.to_list(SCon{Char.from_u32(65279), txt}), Lex.Lex{Lex.Idle{}, [],
          []}))),
        Equal.trans(Bool, wrej(M2.thead(M3.dens(Lex.finish(Lex.run(String.to_list(SCon{Char.from_u32(65279), txt}),
        Lex.Lex{Lex.Idle{}, [], []}))))),
            wrej(M3.den(M2.thead(Lex.finish(Lex.run(String.to_list(SCon{Char.from_u32(65279),
        txt}), Lex.Lex{Lex.Idle{}, [], []}))))), True{},
      Equal.cong(Lex.Tok, Bool, zz => wrej(zz),
          M2.thead(M3.dens(Lex.finish(Lex.run(String.to_list(SCon{Char.from_u32(65279),
        txt}), Lex.Lex{Lex.Idle{}, [], []})))),
            M3.den(M2.thead(Lex.finish(Lex.run(String.to_list(SCon{Char.from_u32(65279),
        txt}), Lex.Lex{Lex.Idle{}, [], []})))), dens_head(Lex.finish(Lex.run(String.to_list(SCon{Char.from_u32(65279),
        txt}), Lex.Lex{Lex.Idle{}, [], []})))),
      bom_go(String.to_list(txt), [])))))))
