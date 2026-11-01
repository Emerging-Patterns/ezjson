# proofs of laws/RawControlCharsRefused.bend
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../src/lex.bend as Lex
import ../src/parse.bend as Parse
import ../laws/RawControlCharsRefused.bend as Laws
import ../laws/defs/CursorAndNumberRules.bend as D1
import ./lemmas/ArrayLength.bend as M1
import ./lemmas/CharacterClasses.bend as M2
import ./lemmas/ErrorToken.bend as M3
import ./lemmas/LexemeOrder.bend as M4
import ./lemmas/LexerErrorSticks.bend as M5
import ./lemmas/OwnedParse.bend as M6
import ./lemmas/StringTokens.bend as M7
import ./lemmas/WellFormedCells.bend as M8

# the character lexer on a string of raw characters it keeps
law raw_lex:
  for +txt: String
  for +h_r: {D1.raw_ok(String.to_list(txt)) == True{} : Bool}
  {Lex.finish(Lex.run(String.to_list("\"" ++ txt ++ "\""), Lex.Lex{Lex.Idle{}, [], []})) == [Lex.TStr{txt}] : List<&2,
    Lex.Tok>}

def raw_lex(txt, h_r):
  Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list("\"" ++ txt ++ "\""), Lex.Lex{Lex.Idle{}, [], []})),
    Lex.finish(Lex.run(String.to_list(txt ++ "\""), Lex.Lex{Lex.Str{}, [], []})), [Lex.TStr{txt}], Equal.cong(Lex.Lex,
    List<&2, Lex.Tok>, zz => Lex.finish(zz), Lex.run(String.to_list("\"" ++ txt ++ "\""), Lex.Lex{Lex.Idle{}, [], []}),
    Lex.run(String.to_list(txt ++ "\""), Lex.Lex{Lex.Str{}, [], []}),
    M7.seq("\"", txt ++ "\"", Lex.Lex{Lex.Idle{}, [], []}, Lex.Lex{Lex.Str{}, [], []}, {==})),
    Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(txt ++ "\""), Lex.Lex{Lex.Str{}, [], []})),
      Lex.finish(Lex.run(String.to_list("\""), Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(txt), []),
      []})), [Lex.TStr{txt}], Equal.cong(Lex.Lex, List<&2, Lex.Tok>, zz => Lex.finish(zz),
      Lex.run(String.to_list(txt ++ "\""), Lex.Lex{Lex.Str{}, [], []}), Lex.run(String.to_list("\""),
      Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(txt), []), []}),
    M7.seq(txt, "\"", Lex.Lex{Lex.Str{}, [], []}, Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(txt), []),
      []}, M7.lex_raw(String.to_list(txt), h_r, [], []))),
    Equal.cong(String, List<&2, Lex.Tok>, zz => [Lex.TStr{zz}], Lex.text(List.reverse.go(&2, Char, String.to_list(txt),
      [])), txt, M4.word_text(txt))))

def Laws.raw_kept(txt, h_r, h_s):
  M7.one_str(Lex.tokens("\"" ++ txt ++ "\""), txt, Equal.trans(List<&2, Lex.Tok>,
      M4.dens(Lex.tokens("\"" ++ txt ++ "\"")),
    M4.dens(Lex.finish(Lex.run(String.to_list("\"" ++ txt ++ "\""), Lex.Lex{Lex.Idle{}, [], []}))), [Lex.TStr{txt}],
    M2.lexers_agree("\"" ++ txt ++ "\"", h_s), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => M4.dens(zz),
      Lex.finish(Lex.run(String.to_list("\"" ++ txt ++ "\""), Lex.Lex{Lex.Idle{}, [], []})), [Lex.TStr{txt}],
      raw_lex(txt, h_r))))

# a control below U+0020 is no hex digit
def nohex_goal(uu: U32) -> Type:
  {Lex.hex.ok(uu) == False{} : Bool}

# nohex, one control at a time
law nohex5:
  for b0: Bool
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  nohex_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, M8.zw(26n)}}}}}}})

def nohex5(b0, b1, b2, b3, b4):
  match b0 b1 b2 b3 b4:
    case False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{}:
      {==}

# nohex, once bit 5 and the bits above are known
law nohex.at:
  for cc: Cmp
  for b5: Bool
  for b0: Bool
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  for +rest: Word(26n)
  for ec: {Word.cmp(26n, rest, M8.zw(26n)) == cc : Cmp}
  for h_lt: {Cmp.is_lt(Word.cmp.fin(b5, True{}, cc)) == True{} : Bool}
  nohex_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}})

def nohex.at(cc, b5, b0, b1, b2, b3, b4, rest, ec, h_lt):
  match cc:
    case LT{}:
      ez = Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Word.cmp(26n, rest, M8.zw(26n)), LT{}, ec)
      Empty.absurd(nohex_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}),
        M1.true_false(Equal.trans(Bool, True{},
        Cmp.is_lt(Word.cmp(26n, rest, M8.zw(26n))), False{},
        Equal.sym(Bool, Cmp.is_lt(Word.cmp(26n, rest, M8.zw(26n))), True{}, ez), M8.zw_nlt(26n, rest))))
    case GT{}:
      match b5:
        case False{}:
          Empty.absurd(nohex_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, rest}}}}}}}),
            M4.false_true(h_lt))
        case True{}:
          Empty.absurd(nohex_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{True{}, rest}}}}}}}),
            M4.false_true(h_lt))
    case EQ{}:
      match b5:
        case True{}:
          Empty.absurd(nohex_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{True{}, rest}}}}}}}),
            M4.false_true(h_lt))
        case False{}:
          er = Equal.sym(Word(26n), rest, M8.zw(26n),
            M8.weq(26n, rest, M8.zw(26n), Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Word.cmp(26n, rest, M8.zw(26n)),
                EQ{}, ec)))
          %er : nohex_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, _}}}}}}})
          nohex5(b0, b1, b2, b3, b4)

# a control below U+0020 is no hex digit, for every code point below U+0020
law nohex:
  for +uu: U32
  for h_lt: {U32.is_lt(uu, 32) == True{} : Bool}
  nohex_goal(uu)

def nohex(uu, h_lt):
  match uu:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, +rest}}}}}}}:
      +c5 = Word.cmp.fin(b5, True{}, Word.cmp(26n, rest, M8.zw(26n)))
      +c4 = Word.cmp.fin(b4, False{}, c5)
      +c3 = Word.cmp.fin(b3, False{}, c4)
      +c2 = Word.cmp.fin(b2, False{}, c3)
      +c1 = Word.cmp.fin(b1, False{}, c2)
      h5 = M8.lt_up(b4, c5, M8.lt_up(b3, c4, M8.lt_up(b2, c3, M8.lt_up(b1, c2, M8.lt_up(b0, c1, h_lt)))))
      nohex.at(Word.cmp(26n, rest, M8.zw(26n)), b5, b0, b1, b2, b3, b4, rest, {==}, h5)

# laws/RawControlCharsRefused.bend: a raw control in a string

# the lexer modes a scan state allows
def okm(cs: Laws.Cs, md: Lex.Mode) -> Bool:
  match cs:
    case Laws.CsOut{}:
      match md:
        case Lex.Idle{}:
          True{}
        case Lex.Word{}:
          True{}
        case Lex.Str{}:
          False{}
        case Lex.Esc{}:
          False{}
        case Lex.Uni{l1, a1}:
          False{}
        case Lex.Hi{h1}:
          False{}
        case Lex.HiEsc{h1}:
          False{}
        case Lex.Lo{l1, a1, h1}:
          False{}
        case Lex.Bad{}:
          True{}
    case Laws.CsIn{}:
      match md:
        case Lex.Idle{}:
          False{}
        case Lex.Word{}:
          False{}
        case Lex.Str{}:
          True{}
        case Lex.Esc{}:
          False{}
        case Lex.Uni{l1, a1}:
          True{}
        case Lex.Hi{h1}:
          True{}
        case Lex.HiEsc{h1}:
          False{}
        case Lex.Lo{l1, a1, h1}:
          True{}
        case Lex.Bad{}:
          True{}
    case Laws.CsEsc{}:
      match md:
        case Lex.Idle{}:
          False{}
        case Lex.Word{}:
          False{}
        case Lex.Str{}:
          False{}
        case Lex.Esc{}:
          True{}
        case Lex.Uni{l1, a1}:
          False{}
        case Lex.Hi{h1}:
          False{}
        case Lex.HiEsc{h1}:
          True{}
        case Lex.Lo{l1, a1, h1}:
          False{}
        case Lex.Bad{}:
          True{}
    case Laws.CsHit{}:
      match md:
        case Lex.Idle{}:
          False{}
        case Lex.Word{}:
          False{}
        case Lex.Str{}:
          False{}
        case Lex.Esc{}:
          False{}
        case Lex.Uni{l1, a1}:
          False{}
        case Lex.Hi{h1}:
          False{}
        case Lex.HiEsc{h1}:
          False{}
        case Lex.Lo{l1, a1, h1}:
          False{}
        case Lex.Bad{}:
          True{}

# a lexer state's mode
def lmode(lx: Lex.Lex) -> Lex.Mode:
  match lx:
    case Lex.Lex{md, _bf, _tk}:
      md

# every scan state allows a rejected text
law okm_bad:
  for cs: Laws.Cs
  {okm(cs, Lex.Bad{}) == True{} : Bool}

def okm_bad(cs):
  match cs:
    case Laws.CsOut{}:
      {==}
    case Laws.CsIn{}:
      {==}
    case Laws.CsEsc{}:
      {==}
    case Laws.CsHit{}:
      {==}

# a raw character in a string, by its control test
law str_ct:
  for ct: Bool
  for +uu: U32
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  {okm(Bool.pick(Laws.Cs, ct, Laws.CsHit{}, Laws.CsIn{}), lmode(Lex.step.str.go(Chr{uu}, bf, tk, ct))) == True{} : Bool}

def str_ct(ct, _uu, _bf, _tk):
  match ct:
    case True{}:
      {==}
    case False{}:
      {==}

# out_idle: one character, by its class
law out_idle:
  for cls: Lex.Class
  for +uu: U32
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +ecls: {Lex.classify(Chr{uu}) == cls : Lex.Class}
  {okm(Bool.pick(Laws.Cs, U32.is_eq(uu, 34), Laws.CsIn{}, Laws.CsOut{}), lmode(Lex.step(Lex.Idle{}, cls, Chr{uu}, bf,
    tk))) == True{} : Bool}

def out_idle(cls, uu, bf, tk, ecls):
  match cls:
    case Lex.CQuote{}:
      ek = Equal.sym(U32, uu, 34, M2.cls_quote(Chr{uu}, ecls))
      %ek : {okm(Bool.pick(Laws.Cs, U32.is_eq(_, 34), Laws.CsIn{}, Laws.CsOut{}), lmode(Lex.step(Lex.Idle{},
        Lex.CQuote{}, Chr{_}, bf, tk))) == True{} : Bool}
      {==}
    case Lex.CBack{}:
      ek = Equal.sym(U32, uu, 92, M2.cls_back(Chr{uu}, ecls))
      %ek : {okm(Bool.pick(Laws.Cs, U32.is_eq(_, 34), Laws.CsIn{}, Laws.CsOut{}), lmode(Lex.step(Lex.Idle{},
        Lex.CBack{}, Chr{_}, bf, tk))) == True{} : Bool}
      {==}
    case Lex.CPunct{+pp}:
      e34 = Equal.sym(Bool, U32.is_eq(uu, 34), False{}, M3.nq(U32.is_eq(uu, 34), uu, Lex.CPunct{pp}, {==}, ecls, {==}))
      %e34 : {okm(Bool.pick(Laws.Cs, _, Laws.CsIn{}, Laws.CsOut{}), lmode(Lex.step(Lex.Idle{}, Lex.CPunct{pp}, Chr{uu},
        bf, tk))) == True{} : Bool}
      {==}
    case Lex.CSpace{}:
      e34 = Equal.sym(Bool, U32.is_eq(uu, 34), False{}, M3.nq(U32.is_eq(uu, 34), uu, Lex.CSpace{}, {==}, ecls, {==}))
      %e34 : {okm(Bool.pick(Laws.Cs, _, Laws.CsIn{}, Laws.CsOut{}), lmode(Lex.step(Lex.Idle{}, Lex.CSpace{}, Chr{uu},
        bf, tk))) == True{} : Bool}
      {==}
    case Lex.COther{}:
      e34 = Equal.sym(Bool, U32.is_eq(uu, 34), False{}, M3.nq(U32.is_eq(uu, 34), uu, Lex.COther{}, {==}, ecls, {==}))
      %e34 : {okm(Bool.pick(Laws.Cs, _, Laws.CsIn{}, Laws.CsOut{}), lmode(Lex.step(Lex.Idle{}, Lex.COther{}, Chr{uu},
        bf, tk))) == True{} : Bool}
      {==}

# out_word: one character, by its class
law out_word:
  for cls: Lex.Class
  for +uu: U32
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +ecls: {Lex.classify(Chr{uu}) == cls : Lex.Class}
  {okm(Bool.pick(Laws.Cs, U32.is_eq(uu, 34), Laws.CsIn{}, Laws.CsOut{}), lmode(Lex.step(Lex.Word{}, cls, Chr{uu}, bf,
    tk))) == True{} : Bool}

def out_word(cls, uu, bf, tk, ecls):
  match cls:
    case Lex.CQuote{}:
      ek = Equal.sym(U32, uu, 34, M2.cls_quote(Chr{uu}, ecls))
      %ek : {okm(Bool.pick(Laws.Cs, U32.is_eq(_, 34), Laws.CsIn{}, Laws.CsOut{}), lmode(Lex.step(Lex.Word{},
        Lex.CQuote{}, Chr{_}, bf, tk))) == True{} : Bool}
      {==}
    case Lex.CBack{}:
      ek = Equal.sym(U32, uu, 92, M2.cls_back(Chr{uu}, ecls))
      %ek : {okm(Bool.pick(Laws.Cs, U32.is_eq(_, 34), Laws.CsIn{}, Laws.CsOut{}), lmode(Lex.step(Lex.Word{},
        Lex.CBack{}, Chr{_}, bf, tk))) == True{} : Bool}
      {==}
    case Lex.CPunct{+pp}:
      e34 = Equal.sym(Bool, U32.is_eq(uu, 34), False{}, M3.nq(U32.is_eq(uu, 34), uu, Lex.CPunct{pp}, {==}, ecls, {==}))
      %e34 : {okm(Bool.pick(Laws.Cs, _, Laws.CsIn{}, Laws.CsOut{}), lmode(Lex.step(Lex.Word{}, Lex.CPunct{pp}, Chr{uu},
        bf, tk))) == True{} : Bool}
      {==}
    case Lex.CSpace{}:
      e34 = Equal.sym(Bool, U32.is_eq(uu, 34), False{}, M3.nq(U32.is_eq(uu, 34), uu, Lex.CSpace{}, {==}, ecls, {==}))
      %e34 : {okm(Bool.pick(Laws.Cs, _, Laws.CsIn{}, Laws.CsOut{}), lmode(Lex.step(Lex.Word{}, Lex.CSpace{}, Chr{uu},
        bf, tk))) == True{} : Bool}
      {==}
    case Lex.COther{}:
      e34 = Equal.sym(Bool, U32.is_eq(uu, 34), False{}, M3.nq(U32.is_eq(uu, 34), uu, Lex.COther{}, {==}, ecls, {==}))
      %e34 : {okm(Bool.pick(Laws.Cs, _, Laws.CsIn{}, Laws.CsOut{}), lmode(Lex.step(Lex.Word{}, Lex.COther{}, Chr{uu},
        bf, tk))) == True{} : Bool}
      {==}

# in_str: one character, by its class
law in_str:
  for cls: Lex.Class
  for +uu: U32
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for +ecls: {Lex.classify(Chr{uu}) == cls : Lex.Class}
  {okm(Bool.pick(Laws.Cs, U32.is_eq(uu, 34), Laws.CsOut{}, Bool.pick(Laws.Cs, U32.is_eq(uu, 92), Laws.CsEsc{},
    Bool.pick(Laws.Cs, U32.is_lt(uu, 32), Laws.CsHit{}, Laws.CsIn{}))), lmode(Lex.step(Lex.Str{}, cls, Chr{uu}, bf,
    tk))) == True{} : Bool}

def in_str(cls, uu, bf, tk, ecls):
  match cls:
    case Lex.CQuote{}:
      ek = Equal.sym(U32, uu, 34, M2.cls_quote(Chr{uu}, ecls))
      %ek : {okm(Bool.pick(Laws.Cs, U32.is_eq(_, 34), Laws.CsOut{}, Bool.pick(Laws.Cs, U32.is_eq(_, 92), Laws.CsEsc{},
        Bool.pick(Laws.Cs, U32.is_lt(_, 32), Laws.CsHit{}, Laws.CsIn{}))), lmode(Lex.step(Lex.Str{}, Lex.CQuote{},
        Chr{_}, bf, tk))) == True{} : Bool}
      {==}
    case Lex.CBack{}:
      ek = Equal.sym(U32, uu, 92, M2.cls_back(Chr{uu}, ecls))
      %ek : {okm(Bool.pick(Laws.Cs, U32.is_eq(_, 34), Laws.CsOut{}, Bool.pick(Laws.Cs, U32.is_eq(_, 92), Laws.CsEsc{},
        Bool.pick(Laws.Cs, U32.is_lt(_, 32), Laws.CsHit{}, Laws.CsIn{}))), lmode(Lex.step(Lex.Str{}, Lex.CBack{},
        Chr{_}, bf, tk))) == True{} : Bool}
      {==}
    case Lex.CPunct{+pp}:
      e34 = Equal.sym(Bool, U32.is_eq(uu, 34), False{}, M3.nq(U32.is_eq(uu, 34), uu, Lex.CPunct{pp}, {==}, ecls, {==}))
      e92 = Equal.sym(Bool, U32.is_eq(uu, 92), False{}, M3.nb(U32.is_eq(uu, 92), uu, Lex.CPunct{pp}, {==}, ecls, {==}))
      %e34 : {okm(Bool.pick(Laws.Cs, _, Laws.CsOut{}, Bool.pick(Laws.Cs, U32.is_eq(uu, 92), Laws.CsEsc{},
        Bool.pick(Laws.Cs, U32.is_lt(uu, 32), Laws.CsHit{}, Laws.CsIn{}))), lmode(Lex.step(Lex.Str{}, Lex.CPunct{pp},
        Chr{uu}, bf, tk))) == True{} : Bool}
      %e92 : {okm(Bool.pick(Laws.Cs, False{}, Laws.CsOut{}, Bool.pick(Laws.Cs, _, Laws.CsEsc{}, Bool.pick(Laws.Cs,
        U32.is_lt(uu, 32), Laws.CsHit{}, Laws.CsIn{}))), lmode(Lex.step(Lex.Str{}, Lex.CPunct{pp}, Chr{uu}, bf,
        tk))) == True{} : Bool}
      str_ct(U32.is_lt(uu, 32), uu, bf, tk)
    case Lex.CSpace{}:
      e34 = Equal.sym(Bool, U32.is_eq(uu, 34), False{}, M3.nq(U32.is_eq(uu, 34), uu, Lex.CSpace{}, {==}, ecls, {==}))
      e92 = Equal.sym(Bool, U32.is_eq(uu, 92), False{}, M3.nb(U32.is_eq(uu, 92), uu, Lex.CSpace{}, {==}, ecls, {==}))
      %e34 : {okm(Bool.pick(Laws.Cs, _, Laws.CsOut{}, Bool.pick(Laws.Cs, U32.is_eq(uu, 92), Laws.CsEsc{},
        Bool.pick(Laws.Cs, U32.is_lt(uu, 32), Laws.CsHit{}, Laws.CsIn{}))), lmode(Lex.step(Lex.Str{}, Lex.CSpace{},
        Chr{uu}, bf, tk))) == True{} : Bool}
      %e92 : {okm(Bool.pick(Laws.Cs, False{}, Laws.CsOut{}, Bool.pick(Laws.Cs, _, Laws.CsEsc{}, Bool.pick(Laws.Cs,
        U32.is_lt(uu, 32), Laws.CsHit{}, Laws.CsIn{}))), lmode(Lex.step(Lex.Str{}, Lex.CSpace{}, Chr{uu}, bf,
        tk))) == True{} : Bool}
      str_ct(U32.is_lt(uu, 32), uu, bf, tk)
    case Lex.COther{}:
      e34 = Equal.sym(Bool, U32.is_eq(uu, 34), False{}, M3.nq(U32.is_eq(uu, 34), uu, Lex.COther{}, {==}, ecls, {==}))
      e92 = Equal.sym(Bool, U32.is_eq(uu, 92), False{}, M3.nb(U32.is_eq(uu, 92), uu, Lex.COther{}, {==}, ecls, {==}))
      %e34 : {okm(Bool.pick(Laws.Cs, _, Laws.CsOut{}, Bool.pick(Laws.Cs, U32.is_eq(uu, 92), Laws.CsEsc{},
        Bool.pick(Laws.Cs, U32.is_lt(uu, 32), Laws.CsHit{}, Laws.CsIn{}))), lmode(Lex.step(Lex.Str{}, Lex.COther{},
        Chr{uu}, bf, tk))) == True{} : Bool}
      %e92 : {okm(Bool.pick(Laws.Cs, False{}, Laws.CsOut{}, Bool.pick(Laws.Cs, _, Laws.CsEsc{}, Bool.pick(Laws.Cs,
        U32.is_lt(uu, 32), Laws.CsHit{}, Laws.CsIn{}))), lmode(Lex.step(Lex.Str{}, Lex.COther{}, Chr{uu}, bf,
        tk))) == True{} : Bool}
      str_ct(U32.is_lt(uu, 32), uu, bf, tk)

# the end of a \u escape stays inside the string
law end_in:
  for key: Lex.Sur
  for +cp: U32
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  {okm(Laws.CsIn{}, lmode(Lex.unicode.end.go(cp, bf, tk, key))) == True{} : Bool}

def end_in(key, _cp, _bf, _tk):
  match key:
    case Lex.SOk{}:
      {==}
    case Lex.SHi{}:
      {==}
    case Lex.SLo{}:
      {==}

# a \u escape's digit stays inside the string
law uni_in:
  for ok: Bool
  for left: Nat
  for +acc: U32
  for +ch: Char
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  {okm(Laws.CsIn{}, lmode(Lex.unicode.go(left, acc, ch, bf, tk, ok))) == True{} : Bool}

def uni_in(ok, left, acc, ch, bf, tk):
  match ok:
    case False{}:
      {==}
    case True{}:
      match left:
        case 0n:
          end_in(Lex.unicode.sur((acc * 16 + Lex.hex(ch) : U32)), (acc * 16 + Lex.hex(ch) : U32), bf, tk)
        case 1n+_pp:
          {==}

# the end of a low surrogate escape stays inside the string
law lowend_in:
  for key: Lex.Sur
  for +lo: U32
  for +hi: U32
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  {okm(Laws.CsIn{}, lmode(Lex.unicode.low.end.go(lo, hi, bf, tk, key))) == True{} : Bool}

def lowend_in(key, _lo, _hi, _bf, _tk):
  match key:
    case Lex.SOk{}:
      {==}
    case Lex.SHi{}:
      {==}
    case Lex.SLo{}:
      {==}

# a low surrogate escape's digit stays inside the string
law low_in:
  for ok: Bool
  for left: Nat
  for +acc: U32
  for +hi: U32
  for +ch: Char
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  {okm(Laws.CsIn{}, lmode(Lex.unicode.low.go(left, acc, hi, ch, bf, tk, ok))) == True{} : Bool}

def low_in(ok, left, acc, hi, ch, bf, tk):
  match ok:
    case False{}:
      {==}
    case True{}:
      match left:
        case 0n:
          lowend_in(Lex.unicode.sur((acc * 16 + Lex.hex(ch) : U32)), (acc * 16 + Lex.hex(ch) : U32), hi, bf, tk)
        case 1n+_pp:
          {==}

# an escaped character's result stays inside the string
law put_in:
  for mb: Maybe<&2, Char>
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  {okm(Laws.CsIn{}, lmode(Lex.escape.put(mb, bf, tk))) == True{} : Bool}

def put_in(mb, _bf, _tk):
  match mb:
    case Some{_ch}:
      {==}
    case None{}:
      {==}

# the character after a backslash stays inside the string
law esc_in:
  for isu: Bool
  for +ch: Char
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  {okm(Laws.CsIn{}, lmode(Lex.escape.go(ch, bf, tk, isu))) == True{} : Bool}

def esc_in(isu, ch, bf, tk):
  match isu:
    case True{}:
      {==}
    case False{}:
      put_in(Lex.unescape(ch), bf, tk)

# the character after a backslash after a high surrogate stays inside the string
law hiesc_in:
  for isu: Bool
  for +hi: U32
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  {okm(Laws.CsIn{}, lmode(Lex.step.hiesc.go(hi, bf, tk, isu))) == True{} : Bool}

def hiesc_in(isu, _hi, _bf, _tk):
  match isu:
    case True{}:
      {==}
    case False{}:
      {==}

# a \u escape's digit, by the character's kind
law in_uni:
  for q: Bool
  for bk: Bool
  for ct: Bool
  for +uu: U32
  for left: Nat
  for +acc: U32
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for eq: {U32.is_eq(uu, 34) == q : Bool}
  for ebk: {U32.is_eq(uu, 92) == bk : Bool}
  for ect: {U32.is_lt(uu, 32) == ct : Bool}
  {okm(Bool.pick(Laws.Cs, q, Laws.CsOut{}, Bool.pick(Laws.Cs, bk, Laws.CsEsc{}, Bool.pick(Laws.Cs, ct, Laws.CsHit{},
    Laws.CsIn{}))), lmode(Lex.unicode.go(left, acc, Chr{uu}, bf, tk, Lex.hex.ok(uu)))) == True{} : Bool}

def in_uni(q, bk, ct, uu, left, acc, bf, tk, eq, ebk, ect):
  match q:
    case True{}:
      ek = Equal.sym(U32, uu, 34, M8.ueq(uu, 34, eq))
      %ek : {okm(Laws.CsOut{}, lmode(Lex.unicode.go(left, acc, Chr{_}, bf, tk, Lex.hex.ok(_)))) == True{} : Bool}
      {==}
    case False{}:
      match bk:
        case True{}:
          ek = Equal.sym(U32, uu, 92, M8.ueq(uu, 92, ebk))
          %ek : {okm(Laws.CsEsc{}, lmode(Lex.unicode.go(left, acc, Chr{_}, bf, tk, Lex.hex.ok(_)))) == True{} : Bool}
          {==}
        case False{}:
          match ct:
            case True{}:
              nh = Equal.sym(Bool, Lex.hex.ok(uu), False{}, nohex(uu, ect))
              %nh : {okm(Laws.CsHit{}, lmode(Lex.unicode.go(left, acc, Chr{uu}, bf, tk, _))) == True{} : Bool}
              {==}
            case False{}:
              uni_in(Lex.hex.ok(uu), left, acc, Chr{uu}, bf, tk)

# a low surrogate escape's digit, by the character's kind
law in_lo:
  for q: Bool
  for bk: Bool
  for ct: Bool
  for +uu: U32
  for left: Nat
  for +acc: U32
  for +hi: U32
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for eq: {U32.is_eq(uu, 34) == q : Bool}
  for ebk: {U32.is_eq(uu, 92) == bk : Bool}
  for ect: {U32.is_lt(uu, 32) == ct : Bool}
  {okm(Bool.pick(Laws.Cs, q, Laws.CsOut{}, Bool.pick(Laws.Cs, bk, Laws.CsEsc{}, Bool.pick(Laws.Cs, ct, Laws.CsHit{},
    Laws.CsIn{}))), lmode(Lex.unicode.low.go(left, acc, hi, Chr{uu}, bf, tk, Lex.hex.ok(uu)))) == True{} : Bool}

def in_lo(q, bk, ct, uu, left, acc, hi, bf, tk, eq, ebk, ect):
  match q:
    case True{}:
      ek = Equal.sym(U32, uu, 34, M8.ueq(uu, 34, eq))
      %ek : {okm(Laws.CsOut{}, lmode(Lex.unicode.low.go(left, acc, hi, Chr{_}, bf, tk,
        Lex.hex.ok(_)))) == True{} : Bool}
      {==}
    case False{}:
      match bk:
        case True{}:
          ek = Equal.sym(U32, uu, 92, M8.ueq(uu, 92, ebk))
          %ek : {okm(Laws.CsEsc{}, lmode(Lex.unicode.low.go(left, acc, hi, Chr{_}, bf, tk,
            Lex.hex.ok(_)))) == True{} : Bool}
          {==}
        case False{}:
          match ct:
            case True{}:
              nh = Equal.sym(Bool, Lex.hex.ok(uu), False{}, nohex(uu, ect))
              %nh : {okm(Laws.CsHit{}, lmode(Lex.unicode.low.go(left, acc, hi, Chr{uu}, bf, tk, _))) == True{} : Bool}
              {==}
            case False{}:
              low_in(Lex.hex.ok(uu), left, acc, hi, Chr{uu}, bf, tk)

# after a high surrogate, a plain character
law in_hi_plain:
  for +hi: U32
  for +uu: U32
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for ebk: {U32.is_eq(uu, 92) == False{} : Bool}
  {okm(Laws.CsIn{}, lmode(Lex.step.hi.go(hi, bf, tk, U32.is_eq(uu, 92)))) == True{} : Bool}

def in_hi_plain(hi, uu, bf, tk, ebk):
  e2 = Equal.sym(Bool, U32.is_eq(uu, 92), False{}, ebk)
  %e2 : {okm(Laws.CsIn{}, lmode(Lex.step.hi.go(hi, bf, tk, _))) == True{} : Bool}
  {==}

# the character after a high surrogate, by its kind
law in_hi:
  for q: Bool
  for bk: Bool
  for ct: Bool
  for +uu: U32
  for +hi: U32
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for eq: {U32.is_eq(uu, 34) == q : Bool}
  for ebk: {U32.is_eq(uu, 92) == bk : Bool}
  for ect: {U32.is_lt(uu, 32) == ct : Bool}
  {okm(Bool.pick(Laws.Cs, q, Laws.CsOut{}, Bool.pick(Laws.Cs, bk, Laws.CsEsc{}, Bool.pick(Laws.Cs, ct, Laws.CsHit{},
    Laws.CsIn{}))), lmode(Lex.step.hi.go(hi, bf, tk, U32.is_eq(uu, 92)))) == True{} : Bool}

def in_hi(q, bk, ct, uu, hi, bf, tk, eq, ebk, _ect):
  match q:
    case True{}:
      ek = Equal.sym(U32, uu, 34, M8.ueq(uu, 34, eq))
      %ek : {okm(Laws.CsOut{}, lmode(Lex.step.hi.go(hi, bf, tk, U32.is_eq(_, 92)))) == True{} : Bool}
      {==}
    case False{}:
      match bk:
        case True{}:
          ek = Equal.sym(U32, uu, 92, M8.ueq(uu, 92, ebk))
          %ek : {okm(Laws.CsEsc{}, lmode(Lex.step.hi.go(hi, bf, tk, U32.is_eq(_, 92)))) == True{} : Bool}
          {==}
        case False{}:
          match ct:
            case True{}:
              e2 = Equal.sym(Bool, U32.is_eq(uu, 92), False{}, ebk)
              %e2 : {okm(Laws.CsHit{}, lmode(Lex.step.hi.go(hi, bf, tk, _))) == True{} : Bool}
              {==}
            case False{}:
              in_hi_plain(hi, uu, bf, tk, ebk)

# one character keeps the scan and the lexer's mode in step
law tr_m:
  for cs: Laws.Cs
  for md: Lex.Mode
  for ch: Char
  for +bf: List<&2, Char>
  for +tk: List<&2, Lex.Tok>
  for h: {okm(cs, md) == True{} : Bool}
  {okm(Laws.cs.step(cs, ch), lmode(Lex.feed(ch, Lex.Lex{md, bf, tk}))) == True{} : Bool}

def tr_m(cs, md, ch, bf, tk, h):
  match cs:
    case Laws.CsOut{}:
      match md:
        case Lex.Idle{}:
          match ch:
            case Chr{+uu}:
              out_idle(Lex.classify(Chr{uu}), uu, bf, tk, {==})
        case Lex.Word{}:
          match ch:
            case Chr{+uu}:
              out_word(Lex.classify(Chr{uu}), uu, bf, tk, {==})
        case Lex.Str{}:
          M4.no({okm(Laws.cs.step(Laws.CsOut{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Str{}, bf,
              tk}))) == True{} : Bool}, h)
        case Lex.Esc{}:
          M4.no({okm(Laws.cs.step(Laws.CsOut{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Esc{}, bf,
              tk}))) == True{} : Bool}, h)
        case Lex.Uni{+l1, +a1}:
          M4.no({okm(Laws.cs.step(Laws.CsOut{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Uni{l1, a1}, bf,
            tk}))) == True{} : Bool}, h)
        case Lex.Hi{+h1}:
          M4.no({okm(Laws.cs.step(Laws.CsOut{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Hi{h1}, bf,
              tk}))) == True{} : Bool},
            h)
        case Lex.HiEsc{+h1}:
          M4.no({okm(Laws.cs.step(Laws.CsOut{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.HiEsc{h1}, bf,
            tk}))) == True{} : Bool}, h)
        case Lex.Lo{+l1, +a1, +h1}:
          M4.no({okm(Laws.cs.step(Laws.CsOut{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Lo{l1, a1, h1}, bf,
            tk}))) == True{} : Bool}, h)
        case Lex.Bad{}:
          match ch:
            case Chr{+uu}:
              okm_bad(Laws.cs.step(Laws.CsOut{}, Chr{uu}))
    case Laws.CsIn{}:
      match md:
        case Lex.Idle{}:
          M4.no({okm(Laws.cs.step(Laws.CsIn{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Idle{}, bf,
              tk}))) == True{} : Bool}, h)
        case Lex.Word{}:
          M4.no({okm(Laws.cs.step(Laws.CsIn{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Word{}, bf,
              tk}))) == True{} : Bool}, h)
        case Lex.Str{}:
          match ch:
            case Chr{+uu}:
              in_str(Lex.classify(Chr{uu}), uu, bf, tk, {==})
        case Lex.Esc{}:
          M4.no({okm(Laws.cs.step(Laws.CsIn{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Esc{}, bf, tk}))) == True{} : Bool},
              h)
        case Lex.Uni{+l1, +a1}:
          match ch:
            case Chr{+uu}:
              in_uni(U32.is_eq(uu, 34), U32.is_eq(uu, 92), U32.is_lt(uu, 32), uu, l1, a1, bf, tk, {==}, {==}, {==})
        case Lex.Hi{+h1}:
          match ch:
            case Chr{+uu}:
              in_hi(U32.is_eq(uu, 34), U32.is_eq(uu, 92), U32.is_lt(uu, 32), uu, h1, bf, tk, {==}, {==}, {==})
        case Lex.HiEsc{+h1}:
          M4.no({okm(Laws.cs.step(Laws.CsIn{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.HiEsc{h1}, bf,
            tk}))) == True{} : Bool}, h)
        case Lex.Lo{+l1, +a1, +h1}:
          match ch:
            case Chr{+uu}:
              in_lo(U32.is_eq(uu, 34), U32.is_eq(uu, 92), U32.is_lt(uu, 32), uu, l1, a1, h1, bf, tk, {==}, {==}, {==})
        case Lex.Bad{}:
          match ch:
            case Chr{+uu}:
              okm_bad(Laws.cs.step(Laws.CsIn{}, Chr{uu}))
    case Laws.CsEsc{}:
      match md:
        case Lex.Idle{}:
          M4.no({okm(Laws.cs.step(Laws.CsEsc{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Idle{}, bf,
              tk}))) == True{} : Bool},
            h)
        case Lex.Word{}:
          M4.no({okm(Laws.cs.step(Laws.CsEsc{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Word{}, bf,
              tk}))) == True{} : Bool},
            h)
        case Lex.Str{}:
          M4.no({okm(Laws.cs.step(Laws.CsEsc{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Str{}, bf,
              tk}))) == True{} : Bool}, h)
        case Lex.Esc{}:
          match ch:
            case Chr{+uu}:
              esc_in(U32.is_eq(uu, 117), Chr{uu}, bf, tk)
        case Lex.Uni{+l1, +a1}:
          M4.no({okm(Laws.cs.step(Laws.CsEsc{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Uni{l1, a1}, bf,
            tk}))) == True{} : Bool}, h)
        case Lex.Hi{+h1}:
          M4.no({okm(Laws.cs.step(Laws.CsEsc{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Hi{h1}, bf,
              tk}))) == True{} : Bool},
            h)
        case Lex.HiEsc{+h1}:
          match ch:
            case Chr{+uu}:
              hiesc_in(U32.is_eq(uu, 117), h1, bf, tk)
        case Lex.Lo{+l1, +a1, +h1}:
          M4.no({okm(Laws.cs.step(Laws.CsEsc{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Lo{l1, a1, h1}, bf,
            tk}))) == True{} : Bool}, h)
        case Lex.Bad{}:
          match ch:
            case Chr{+uu}:
              okm_bad(Laws.cs.step(Laws.CsEsc{}, Chr{uu}))
    case Laws.CsHit{}:
      match md:
        case Lex.Idle{}:
          M4.no({okm(Laws.cs.step(Laws.CsHit{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Idle{}, bf,
              tk}))) == True{} : Bool},
            h)
        case Lex.Word{}:
          M4.no({okm(Laws.cs.step(Laws.CsHit{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Word{}, bf,
              tk}))) == True{} : Bool},
            h)
        case Lex.Str{}:
          M4.no({okm(Laws.cs.step(Laws.CsHit{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Str{}, bf,
              tk}))) == True{} : Bool}, h)
        case Lex.Esc{}:
          M4.no({okm(Laws.cs.step(Laws.CsHit{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Esc{}, bf,
              tk}))) == True{} : Bool}, h)
        case Lex.Uni{+l1, +a1}:
          M4.no({okm(Laws.cs.step(Laws.CsHit{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Uni{l1, a1}, bf,
            tk}))) == True{} : Bool}, h)
        case Lex.Hi{+h1}:
          M4.no({okm(Laws.cs.step(Laws.CsHit{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Hi{h1}, bf,
              tk}))) == True{} : Bool},
            h)
        case Lex.HiEsc{+h1}:
          M4.no({okm(Laws.cs.step(Laws.CsHit{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.HiEsc{h1}, bf,
            tk}))) == True{} : Bool}, h)
        case Lex.Lo{+l1, +a1, +h1}:
          M4.no({okm(Laws.cs.step(Laws.CsHit{}, ch), lmode(Lex.feed(ch, Lex.Lex{Lex.Lo{l1, a1, h1}, bf,
            tk}))) == True{} : Bool}, h)
        case Lex.Bad{}:
          match ch:
            case Chr{+uu}:
              okm_bad(Laws.cs.step(Laws.CsHit{}, Chr{uu}))

# one character keeps the scan and the lexer in step
law tr1:
  for +cs: Laws.Cs
  for lx: Lex.Lex
  for +ch: Char
  for h: {okm(cs, lmode(lx)) == True{} : Bool}
  {okm(Laws.cs.step(cs, ch), lmode(Lex.feed(ch, lx))) == True{} : Bool}

def tr1(cs, lx, ch, h):
  match lx:
    case Lex.Lex{md, bf, tk}:
      tr_m(cs, md, ch, bf, tk, h)

# every character keeps the scan and the lexer in step
law tr_run:
  for +cs: List<&2, Char>
  for +st: Laws.Cs
  for +lx: Lex.Lex
  for h: {okm(st, lmode(lx)) == True{} : Bool}
  {okm(Laws.cs.run(cs, st), lmode(Lex.run(cs, lx))) == True{} : Bool}

def tr_run(cs, st, lx, h):
  match cs:
    case Nil{}:
      h
    case +hd <> +tl:
      tr_run(tl, Laws.cs.step(st, hd), Lex.feed(hd, lx), tr1(st, lx, hd, h))

# a scan that met a raw control leaves the lexer rejecting
law hit_bad:
  for cs: Laws.Cs
  for md: Lex.Mode
  for hh: {Laws.cs.hit(cs) == True{} : Bool}
  for ho: {okm(cs, md) == True{} : Bool}
  {md == Lex.Bad{} : Lex.Mode}

def hit_bad(cs, md, hh, ho):
  match cs:
    case Laws.CsOut{}:
      Empty.absurd({md == Lex.Bad{} : Lex.Mode}, M4.false_true(hh))
    case Laws.CsIn{}:
      Empty.absurd({md == Lex.Bad{} : Lex.Mode}, M4.false_true(hh))
    case Laws.CsEsc{}:
      Empty.absurd({md == Lex.Bad{} : Lex.Mode}, M4.false_true(hh))
    case Laws.CsHit{}:
      match md:
        case Lex.Idle{}:
          Empty.absurd({Lex.Idle{} == Lex.Bad{} : Lex.Mode}, M4.false_true(ho))
        case Lex.Word{}:
          Empty.absurd({Lex.Word{} == Lex.Bad{} : Lex.Mode}, M4.false_true(ho))
        case Lex.Str{}:
          Empty.absurd({Lex.Str{} == Lex.Bad{} : Lex.Mode}, M4.false_true(ho))
        case Lex.Esc{}:
          Empty.absurd({Lex.Esc{} == Lex.Bad{} : Lex.Mode}, M4.false_true(ho))
        case Lex.Uni{_l1, _a1}:
          Empty.absurd({Lex.Uni{_l1, _a1} == Lex.Bad{} : Lex.Mode}, M4.false_true(ho))
        case Lex.Hi{_h1}:
          Empty.absurd({Lex.Hi{_h1} == Lex.Bad{} : Lex.Mode}, M4.false_true(ho))
        case Lex.HiEsc{_h1}:
          Empty.absurd({Lex.HiEsc{_h1} == Lex.Bad{} : Lex.Mode}, M4.false_true(ho))
        case Lex.Lo{_l1, _a1, _h1}:
          Empty.absurd({Lex.Lo{_l1, _a1, _h1} == Lex.Bad{} : Lex.Mode}, M4.false_true(ho))
        case Lex.Bad{}:
          {==}

# a rejecting lexer's tokens hold the error token
law fin_has_bad:
  for lx: Lex.Lex
  for e: {lmode(lx) == Lex.Bad{} : Lex.Mode}
  {M3.has_bad(Lex.finish(lx)) == True{} : Bool}

def fin_has_bad(lx, e):
  match lx:
    case Lex.Lex{md, +bf, +tk}:
      es = Equal.sym(Lex.Mode, md, Lex.Bad{}, e)
      %es : {M3.has_bad(Lex.finish(Lex.Lex{_, bf, tk})) == True{} : Bool}
      M3.hb_rev(tk, [Lex.TBad{}], {==})

def Laws.ctl_none(txt, h_c, h_s):
  M5.own_m_none(Ezjson.parse(txt),
    Equal.trans(Maybe<&2, V.Json>, D1.own_m(Parse.finish(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{},
      Nil{}}))), Parse.finish(M6.ownp(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}}))), None{},
      M6.fin_own(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}})),
      Equal.trans(Maybe<&2, V.Json>, Parse.finish(M6.ownp(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}}))),
        Parse.finish(Parse.run(M4.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}})), None{}, Equal.cong(Parse.P,
        Maybe<&2, V.Json>, zz => Parse.finish(zz), M6.ownp(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}})),
        Parse.run(M4.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}}),
      M6.run_own(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}})),
      Equal.trans(Maybe<&2, V.Json>, Parse.finish(Parse.run(M4.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}})),
        Parse.finish(Parse.run(M4.dens(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))),
        Parse.P{False{}, None{}, Nil{}})), None{}, Equal.cong(List<&2, Lex.Tok>, Maybe<&2, V.Json>,
        zz => Parse.finish(Parse.run(zz, Parse.P{False{}, None{}, Nil{}})), M4.dens(Lex.tokens(txt)),
        M4.dens(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))), M2.lexers_agree(txt, h_s)),
      M3.bad_none(M4.dens(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))), Parse.P{False{},
          None{},
        Nil{}}, Equal.trans(Bool, M3.has_bad(M4.dens(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [],
            []})))),
        M3.has_bad(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))), True{},
        M3.hb_dens(Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))),
      fin_has_bad(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}), hit_bad(Laws.cs.run(String.to_list(txt),
        Laws.CsOut{}),
        lmode(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []})), h_c, tr_run(String.to_list(txt),
          Laws.CsOut{}, Lex.Lex{Lex.Idle{}, [], []}, {==})))))))))
