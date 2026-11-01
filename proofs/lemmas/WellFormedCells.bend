# whitespace, well-formed cells and their tokens
import Base
import ../../src/value.bend as V
import ../../src/lazy.bend as Lazy
import ../../src/lex.bend as Lex
import ../../src/parse.bend as Parse
import ../../src/pull.bend as Pull
import ../../laws/ParsesExactlyJsonTexts.bend as L1
import ../../laws/defs/CursorAndNumberRules.bend as D1
import ../../laws/defs/GrammarDerivations.bend as D2
import ./ArrayLength.bend as M1
import ./LexemeOrder.bend as M2

# a bit compares equal to itself
law fin_self:
  for bb: Bool
  {Word.cmp.fin(bb, bb, EQ{}) == EQ{} : Cmp}

def fin_self(bb):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# words compare equal to themselves
law weq_refl:
  for n: Nat
  for +ww: Word(n)
  {Word.cmp(n, ww, ww) == EQ{} : Cmp}

def weq_refl(n, ww):
  match n:
    case 0n:
      {==}
    case 1n+pp:
      match ww:
        case WCon{bb, tt}:
          ih = Equal.sym(Cmp, Word.cmp(pp, tt, tt), EQ{}, weq_refl(pp, tt))
          %ih : {Word.cmp.fin(bb, bb, _) == EQ{} : Cmp}
          fin_self(bb)

# a character compares equal to itself
law char_eq_refl:
  for +ch: Char
  {Char.is_eq(ch, ch) == True{} : Bool}

def char_eq_refl(ch):
  match ch:
    case Chr{U32{ww}}:
      rf = Equal.sym(Cmp, Word.cmp(32n, ww, ww), EQ{}, weq_refl(32n, ww))
      %rf : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# words that compare equal, bit by bit past the first: the rest equal, the
# first bits the same. From bolt's cfg4.weq.arm
law weq.arm:
  for -pp: Nat
  for -at: Word(pp)
  for -bt: Word(pp)
  for cc: Cmp
  for ec: {Word.cmp(pp, at, bt) == cc : Cmp}
  for ih: {Cmp.is_eq(Word.cmp(pp, at, bt)) == True{} : Bool} -> {at == bt : Word(pp)}
  for ab: Bool
  for bb: Bool
  for ee: {Cmp.is_eq(Word.cmp.fin(ab, bb, cc)) == True{} : Bool}
  {WCon{ab, at} == WCon{bb, bt} : Word.Con<pp>}

def weq.arm(pp, at, bt, cc, ec, ih, ab, bb, ee):
  match cc:
    case LT{}:
      Empty.absurd({WCon{ab, at} == WCon{bb, bt} : Word.Con<pp>}, M2.false_true(ee))
    case GT{}:
      Empty.absurd({WCon{ab, at} == WCon{bb, bt} : Word.Con<pp>}, M2.false_true(ee))
    case EQ{}:
      match ab bb:
        case False{} False{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{False{}, ww}, at, bt,
            ih(Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Word.cmp(pp, at, bt), EQ{}, ec)))
        case True{} True{}:
          Equal.cong(Word(pp), Word.Con<pp>, ww => WCon{True{}, ww}, at, bt,
            ih(Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Word.cmp(pp, at, bt), EQ{}, ec)))
        case False{} True{}:
          Empty.absurd({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<pp>}, M2.false_true(ee))
        case True{} False{}:
          Empty.absurd({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<pp>}, M2.false_true(ee))

# words that compare equal are equal. From bolt's cfg4.weq
law weq:
  for n: Nat
  for aw: Word(n)
  for bw: Word(n)
  for ee: {Cmp.is_eq(Word.cmp(n, aw, bw)) == True{} : Bool}
  {aw == bw : Word(n)}

def weq(n, aw, bw, ee):
  match n:
    case 0n:
      match aw bw:
        case WNil{} WNil{}:
          {==}
    case 1n+(+pp):
      match aw bw:
        case WCon{ab, +at} WCon{bb, +bt}:
          weq.arm(pp, at, bt, Word.cmp(pp, at, bt), {==}, xx => weq(pp, at, bt, xx), ab, bb, ee)

# U32s that compare equal are equal. From bolt's cfg4.ueq
law ueq:
  for au: U32
  for bu: U32
  for ee: {U32.is_eq(au, bu) == True{} : Bool}
  {au == bu : U32}

def ueq(au, bu, ee):
  match au bu:
    case U32{xw} U32{yw}:
      Equal.cong(Word(32n), U32, ww => U32{ww}, xw, yw, weq(32n, xw, yw, ee))

# find.eq holds of a string and itself
law find_eq_refl:
  for +txt: String
  {V.find.eq.go(txt, txt, True{}) == True{} : Bool}

def find_eq_refl(txt):
  match txt:
    case SNil{}:
      {==}
    case SCon{ch, tl}:
      rf = Equal.sym(Bool, Char.is_eq(ch, ch), True{}, char_eq_refl(ch))
      %rf : {V.find.eq.go(tl, tl, _) == True{} : Bool}
      find_eq_refl(tl)

# two strings whose first characters' codes are equal and whose rests are equal
law find_eq_cons:
  for +xu: U32
  for +yu: U32
  for -xs: String
  for -ys: String
  for got: ({U32.is_eq(xu, yu) == True{} : Bool} & {xs == ys : String})
  {SCon{Chr{xu}, xs} == SCon{Chr{yu}, ys} : String}

def find_eq_cons(xu, yu, xs, ys, got):
  (eu, es) = got
  ex = ueq(xu, yu, eu)
  %ex : {SCon{Chr{xu}, xs} == SCon{Chr{_}, ys} : String}
  %es : {SCon{Chr{xu}, xs} == SCon{Chr{xu}, _} : String}
  {==}

# find.eq holds only of equal strings, and only while the characters so far agreed
law find_eq_sound:
  for +lhs: String
  for +rhs: String
  for same: Bool
  for ee: {V.find.eq.go(lhs, rhs, same) == True{} : Bool}
  ({same == True{} : Bool} & {lhs == rhs : String})

def find_eq_sound(lhs, rhs, same, ee):
  match lhs rhs same:
    case SNil{} SNil{} True{}:
      ({==}, {==})
    case SNil{} SNil{} False{}:
      Empty.absurd(({False{} == True{} : Bool} & {SNil{} == SNil{} : String}), M2.false_true(ee))
    case SNil{} SCon{hh, tt} sm:
      Empty.absurd(({sm == True{} : Bool} & {SNil{} == SCon{hh, tt} : String}), M2.false_true(ee))
    case SCon{hh, tt} SNil{} sm:
      Empty.absurd(({sm == True{} : Bool} & {SCon{hh, tt} == SNil{} : String}), M2.false_true(ee))
    case SCon{Chr{+xu}, +xs} SCon{Chr{+yu}, +ys} True{}:
      ({==}, find_eq_cons(xu, yu, xs, ys, find_eq_sound(xs, ys, U32.is_eq(xu, yu), ee)))
    case SCon{xc, xs} SCon{yc, ys} False{}:
      Empty.absurd(({False{} == True{} : Bool} & {SCon{xc, xs} == SCon{yc, ys} : String}), M2.false_true(ee))

# find.eq holding of two different strings is impossible
law find_eq_clash:
  for -lhs: String
  for -rhs: String
  for got: ({True{} == True{} : Bool} & {lhs == rhs : String})
  for h_ne: {lhs != rhs : String}
  Empty

def find_eq_clash(_lhs, _rhs, got, h_ne):
  (_st, same) = got
  h_ne(same)

# find.eq is false of two different strings, once its answer is named
law find_eq_false.at:
  for +lhs: String
  for +rhs: String
  for bb: Bool
  for eb: {V.find.eq.go(lhs, rhs, True{}) == bb : Bool}
  for h_ne: {lhs != rhs : String}
  {V.find.eq.go(lhs, rhs, True{}) == False{} : Bool}

def find_eq_false.at(lhs, rhs, bb, eb, h_ne):
  match bb:
    case False{}:
      eb
    case True{}:
      Empty.absurd({V.find.eq.go(lhs, rhs, True{}) == False{} : Bool},
        find_eq_clash(lhs, rhs, find_eq_sound(lhs, rhs, True{}, eb), h_ne))

# find.eq is false of two different strings
law find_eq_false:
  for +lhs: String
  for +rhs: String
  for h_ne: {lhs != rhs : String}
  {V.find.eq.go(lhs, rhs, True{}) == False{} : Bool}

def find_eq_false(lhs, rhs, h_ne):
  find_eq_false.at(lhs, rhs, V.find.eq.go(lhs, rhs, True{}), {==}, h_ne)

# what is left of `src` after its first `nn` characters, counted as span.str
# counts them
def sdrop(src: String, +nn: U32, zero: Bool) -> String:
  match src zero:
    case ss True{}:
      ss
    case SNil{} False{}:
      SNil{}
    case SCon{_, tl} False{}:
      sdrop(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)))

# WP-L2: the character lexer reads back what print writes

# a word of n zero bits
def zw(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+pp:
      WCon{False{}, zw(pp)}

# against a 0 bit, a word is below exactly when the bits above are
law lt_fin_f:
  for cc: Cmp
  for aa: Bool
  {Cmp.is_lt(Word.cmp.fin(aa, False{}, cc)) == Cmp.is_lt(cc) : Bool}

def lt_fin_f(cc, aa):
  match cc:
    case LT{}:
      {==}
    case GT{}:
      {==}
    case EQ{}:
      match aa:
        case False{}:
          {==}
        case True{}:
          {==}

# a word is never below zero
law zw_nlt:
  for n: Nat
  for ww: Word(n)
  {Cmp.is_lt(Word.cmp(n, ww, zw(n))) == False{} : Bool}

def zw_nlt(n, ww):
  match n:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match ww:
        case WCon{bb, +tt}:
          Equal.trans(Bool, Cmp.is_lt(Word.cmp.fin(bb, False{}, Word.cmp(pp, tt, zw(pp)))),
            Cmp.is_lt(Word.cmp(pp, tt, zw(pp))), False{}, lt_fin_f(Word.cmp(pp, tt, zw(pp)), bb), zw_nlt(pp, tt))

# below a word whose low bit is 0, the bits above are below
law lt_up:
  for aa: Bool
  for cc: Cmp
  for h_lt: {Cmp.is_lt(Word.cmp.fin(aa, False{}, cc)) == True{} : Bool}
  {Cmp.is_lt(cc) == True{} : Bool}

def lt_up(aa, cc, h_lt):
  Equal.trans(Bool, Cmp.is_lt(cc), Cmp.is_lt(Word.cmp.fin(aa, False{}, cc)), True{},
    Equal.sym(Bool, Cmp.is_lt(Word.cmp.fin(aa, False{}, cc)), Cmp.is_lt(cc), lt_fin_f(cc, aa)), h_lt)

# reversing onto an accumulator goes through an append
law rev_app:
  for +aa: List<&2, Lex.Tok>
  for +bb: List<&2, Lex.Tok>
  for +acc: List<&2, Lex.Tok>
  {List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, aa, bb), acc) ==
    List.reverse.go(&2, Lex.Tok, bb, List.reverse.go(&2, Lex.Tok, aa, acc)) : List<&2, Lex.Tok>}

def rev_app(aa, bb, acc):
  match aa:
    case Nil{}:
      {==}
    case Con{+hd, +tl}:
      rev_app(tl, bb, hd <> acc)

# tj with each string as it is, not fixed as print writes it: the tokens a value is: by shape, a value, an array's
# cells, or an object's cells. Strings are fixed as print writes them
def tj_r(val: V.Json, sh: V.Shape) -> List<&2, Lex.Tok>:
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
      [Lex.TStr{txt}]
    case V.JSpan{src, +nn} V.WVal{}:
      [Lex.TStr{V.span.str(src, nn, U32.is_zero(nn))}]
    case V.JArr{items} V.WVal{}:
      Lex.TOpenArr{} <> List.append(&2, Lex.Tok, tj_r(items, V.WArr{}), [Lex.TCloseArr{}])
    case V.JObj{pairs} V.WVal{}:
      Lex.TOpenObj{} <> List.append(&2, Lex.Tok, tj_r(pairs, V.WObj{}), [Lex.TCloseObj{}])
    case V.JNil{} V.WArr{}:
      []
    case V.JCons{hd, V.JNil{}} V.WArr{}:
      tj_r(hd, V.WVal{})
    case V.JCons{hd, tl} V.WArr{}:
      List.append(&2, Lex.Tok, tj_r(hd, V.WVal{}), Lex.TComma{} <> tj_r(tl, V.WArr{}))
    case V.JNil{} V.WObj{}:
      []
    case V.JPair{kk, vv, V.JNil{}} V.WObj{}:
      Lex.TStr{kk} <> Lex.TColon{} <> tj_r(vv, V.WVal{})
    case V.JPair{kk, vv, rr} V.WObj{}:
      Lex.TStr{kk} <> Lex.TColon{} <>
        List.append(&2, Lex.Tok, tj_r(vv, V.WVal{}), Lex.TComma{} <> tj_r(rr, V.WObj{}))
    case V.JBind{src, +nn, vv, V.JNil{}} V.WObj{}:
      Lex.TStr{V.span.str(src, nn, U32.is_zero(nn))} <> Lex.TColon{} <> tj_r(vv, V.WVal{})
    case V.JBind{src, +nn, vv, rr} V.WObj{}:
      Lex.TStr{V.span.str(src, nn, U32.is_zero(nn))} <> Lex.TColon{} <>
        List.append(&2, Lex.Tok, tj_r(vv, V.WVal{}), Lex.TComma{} <> tj_r(rr, V.WObj{}))
    case _ _:
      []

# a well-formed value in front of well-formed cells
law cons_wf:
  for +vv: V.Json
  for +items: V.Json
  for hv: {V.wf(vv) == True{} : Bool}
  for hi: {V.wf.go(items, V.WArr{}) == True{} : Bool}
  {V.wf.go(V.JCons{vv, items}, V.WArr{}) == True{} : Bool}

def cons_wf(vv, items, hv, hi):
  hs = Equal.sym(Bool, V.wf(vv), True{}, hv)
  %hs : {Lazy.stop(Bool, Bool.not(_), False{}, _u => V.wf.go(items, V.WArr{})) == True{} : Bool}
  hi

# a well-formed value under a key, in front of well-formed cells
law pair_wf:
  for key: Parse.Key
  for +vv: V.Json
  for +pairs: V.Json
  for hv: {V.wf(vv) == True{} : Bool}
  for hp: {V.wf.go(pairs, V.WObj{}) == True{} : Bool}
  {V.wf.go(Parse.put.pair(key, vv, pairs), V.WObj{}) == True{} : Bool}

def pair_wf(key, vv, pairs, hv, hp):
  match key:
    case Parse.KOwn{_txt}:
      hs = Equal.sym(Bool, V.wf(vv), True{}, hv)
      %hs : {Lazy.stop(Bool, Bool.not(_), False{}, _u => V.wf.go(pairs, V.WObj{})) == True{} : Bool}
      hp
    case Parse.KCut{_src, _nn}:
      hs = Equal.sym(Bool, V.wf(vv), True{}, hv)
      %hs : {Lazy.stop(Bool, Bool.not(_), False{}, _u => V.wf.go(pairs, V.WObj{})) == True{} : Bool}
      hp

# a word character is not a code point classify tests
law neq_cls:
  for bb: Bool
  for +uu: U32
  for +kk: U32
  for eb: {U32.is_eq(uu, kk) == bb : Bool}
  for h: {Lex.classify.go(uu) == Lex.COther{} : Lex.Class}
  for hk: {M2.is_other(Lex.classify.go(kk)) == False{} : Bool}
  {U32.is_eq(uu, kk) == False{} : Bool}

def neq_cls(bb, uu, kk, eb, h, hk):
  match bb:
    case False{}:
      eb
    case True{}:
      Empty.absurd({U32.is_eq(uu, kk) == False{} : Bool}, M1.true_false(Equal.trans(Bool, True{},
        M2.is_other(Lex.classify.go(uu)), False{}, Equal.sym(Bool, M2.is_other(Lex.classify.go(uu)), True{},
          Equal.cong(Lex.Class, Bool, zz => M2.is_other(zz), Lex.classify.go(uu), Lex.COther{}, h)),
        Equal.trans(Bool, M2.is_other(Lex.classify.go(uu)), M2.is_other(Lex.classify.go(kk)), False{},
          Equal.cong(U32, Bool, zz => M2.is_other(Lex.classify.go(zz)), uu, kk, ueq(uu, kk, eb)), hk))))

# the tokens of an array's cells after an element
def ct(rr: D2.Gv) -> List<&2, Lex.Tok>:
  match rr:
    case D2.GEnd{}:
      []
    case other:
      Lex.TComma{} <> tj_r(L1.g.val(other), V.WArr{})

# a punctuation class's token
def ptok.go(cls: Lex.Class) -> Lex.Tok:
  match cls:
    case Lex.CPunct{tt}:
      tt
    case _:
      Lex.TBad{}

# a punctuation character's token
def ptok(ch: Char) -> Lex.Tok:
  ptok.go(Lex.classify(ch))

# a lexeme's token
def lxtok(lx: M2.Lx) -> Lex.Tok:
  match lx:
    case M2.LP{ch}:
      ptok(ch)
    case M2.LW{w}:
      Lex.TWord{w}
    case M2.LS{ps}:
      Lex.TStr{D2.spelled(ps)}

# lexemes' tokens, in the order the lexemes are listed
def rtoks(its: List<&2, M2.It>) -> List<&2, Lex.Tok>:
  match its:
    case Nil{}:
      []
    case M2.It{_, lx} <> rest:
      lxtok(lx) <> rtoks(rest)

# every character is whitespace
def allws(cs: List<&2, Char>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case ch <> tl:
      Bool.and(D1.is_ws(ch), allws(tl))

# a lexeme is well spelled: a string's pieces are
def lxok(lx: M2.Lx) -> Bool:
  match lx:
    case M2.LS{ps}:
      D2.spell_ok(ps)
    case _:
      True{}

# every lexeme is well spelled and follows whitespace
def itsok(its: List<&2, M2.It>) -> Bool:
  match its:
    case Nil{}:
      True{}
    case M2.It{rws, lx} <> rest:
      Bool.and(allws(rws), Bool.and(lxok(lx), itsok(rest)))

# the characters pieces listed last first stand for, last first
def pchars(ps: List<&2, D2.Piece>) -> List<&2, Char>:
  match ps:
    case Nil{}:
      []
    case pc <> rest:
      D2.piece.char(pc) <> pchars(rest)

# the lexer's state between tokens: its tokens are the lexemes', and each
# lexeme is well spelled and follows whitespace, as does what is read since
def ic(its: List<&2, M2.It>, rws: List<&2, Char>, toks: List<&2, Lex.Tok>) -> Type:
  ({toks == rtoks(its) : List<&2, Lex.Tok>} & ({itsok(its) == True{} : Bool} & {allws(rws) == True{} : Bool}))

# the lexer's state inside a string: ic, and its buffer holds the characters
# of well spelled pieces
def sc(
  its: List<&2, M2.It>,
  rws: List<&2, Char>,
  ps: List<&2, D2.Piece>,
  buf: List<&2, Char>,
  toks: List<&2, Lex.Tok>
) -> Type:
  (ic(its, rws, toks) & ({buf == pchars(ps) : List<&2, Char>} & {D2.spell_ok(ps) == True{} : Bool}))

# what a string mode holds, with `x` left to read: the characters decoded so
# far, reversed as `bb`. After the opening quote nothing is held; a span holds
# the characters it covers; a copy holds its buffer
def hold(m: Pull.Mode, x: String, bb: List<&2, Char>) -> Type:
  match m:
    case Pull.MQuote{}:
      ({bb == [] : List<&2, Char>} & {D1.short(x) == True{} : Bool})
    case Pull.MSpan{+cut, +nn}:
      ({sdrop(cut, nn, U32.is_zero(nn)) == x : String}
        & ({Lex.tokens.rev(cut, nn, U32.is_zero(nn), []) == bb : List<&2, Char>} & {D1.short(cut) == True{} : Bool}))
    case Pull.MCopy{buf}:
      {buf == bb : List<&2, Char>}
    case _:
      Empty
