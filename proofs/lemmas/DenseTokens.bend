# a value's tokens read out dense, and fixing their strings
import Base
import ../../src/value.bend as V
import ../../src/lex.bend as Lex
import ../../laws/defs/CursorAndNumberRules.bend as D1
import ./CharacterClasses.bend as M1
import ./LexemeOrder.bend as M2
import ./NumberCharsAreWordChars.bend as M3
import ./WellFormedCells.bend as M4
import ./WordLexing.bend as M5

# a JSON number's characters, from between tokens, make a word
law lex_numl:
  for +cs: List<&2, Char>
  for hn: {D1.number(cs) == True{} : Bool}
  for +toks: List<&2, Lex.Tok>
  {Lex.run(cs, Lex.Lex{Lex.Idle{}, [], toks}) == Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, cs, []), toks} : Lex.Lex}

def lex_numl(cs, hn, toks):
  match cs:
    case Nil{}:
      M2.no({Lex.run([], Lex.Lex{Lex.Idle{}, [], toks}) == Lex.Lex{Lex.Word{}, [], toks} : Lex.Lex}, hn)
    case Con{+hd, +tl}:
      M5.lex_word(hd, tl, M3.oth_number(hd <> tl, hn), toks)

# reversing twice gives back the list
law rev_rev:
  for +xs: List<&2, Lex.Tok>
  for +acc: List<&2, Lex.Tok>
  for +ys: List<&2, Lex.Tok>
  {List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, xs, acc), ys) ==
    List.reverse.go(&2, Lex.Tok, acc, List.append(&2, Lex.Tok, xs, ys)) : List<&2, Lex.Tok>}

def rev_rev(xs, acc, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+hd, +tl}:
      rev_rev(tl, hd <> acc, ys)

# two appends of equal parts are equal
law app_cong:
  for aa: List<&2, Lex.Tok>
  for a2: List<&2, Lex.Tok>
  for bb: List<&2, Lex.Tok>
  for b2: List<&2, Lex.Tok>
  for ea: {aa == a2 : List<&2, Lex.Tok>}
  for eb: {bb == b2 : List<&2, Lex.Tok>}
  {List.append(&2, Lex.Tok, aa, bb) == List.append(&2, Lex.Tok, a2, b2) : List<&2, Lex.Tok>}

def app_cong(aa, _a2, bb, b2, ea, eb):
  %ea : {List.append(&2, Lex.Tok, aa, bb) == List.append(&2, Lex.Tok, _, b2) : List<&2, Lex.Tok>}
  %eb : {List.append(&2, Lex.Tok, aa, bb) == List.append(&2, Lex.Tok, aa, _) : List<&2, Lex.Tok>}
  {==}

# appending nothing
law lapp_nil:
  for +xs: List<&2, Lex.Tok>
  {List.append(&2, Lex.Tok, xs, []) == xs : List<&2, Lex.Tok>}

def lapp_nil(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{hd, +tl}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => hd <> yy, List.append(&2, Lex.Tok, tl, []), tl,
        lapp_nil(tl))

# spans replaced in two token lists joined by a comma, each without spans
law dens_sep:
  for +aa: List<&2, Lex.Tok>
  for +bb: List<&2, Lex.Tok>
  for ea: {M2.dens(aa) == aa : List<&2, Lex.Tok>}
  for eb: {M2.dens(bb) == bb : List<&2, Lex.Tok>}
  {M2.dens(List.append(&2, Lex.Tok, aa, Lex.TComma{} <> bb)) == List.append(&2, Lex.Tok, aa,
    Lex.TComma{} <> bb) : List<&2, Lex.Tok>}

def dens_sep(aa, bb, ea, eb):
  Equal.trans(List<&2, Lex.Tok>, M2.dens(List.append(&2, Lex.Tok, aa, Lex.TComma{} <> bb)),
    List.append(&2, Lex.Tok, M2.dens(aa), Lex.TComma{} <> M2.dens(bb)), List.append(&2, Lex.Tok, aa,
        Lex.TComma{} <> bb),
    M1.dens_app(aa, Lex.TComma{} <> bb),
    app_cong(M2.dens(aa), aa, Lex.TComma{} <> M2.dens(bb), Lex.TComma{} <> bb, ea,
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TComma{} <> yy, M2.dens(bb), bb, eb)))

# a value with its strings fixed as print writes them, and its spans and
# bound keys as owned strings, by shape as tj reads it
def fxv(val: V.Json, sh: V.Shape) -> V.Json:
  match val sh:
    case V.JStr{txt} V.WVal{}:
      V.JStr{M2.fixs(String.to_list(txt))}
    case V.JSpan{src, +nn} V.WVal{}:
      V.JStr{M2.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))}
    case V.JArr{items} V.WVal{}:
      V.JArr{fxv(items, V.WArr{})}
    case V.JObj{pairs} V.WVal{}:
      V.JObj{fxv(pairs, V.WObj{})}
    case V.JCons{hd, tl} V.WArr{}:
      V.JCons{fxv(hd, V.WVal{}), fxv(tl, V.WArr{})}
    case V.JPair{kk, vv, rr} V.WObj{}:
      V.JPair{M2.fixs(String.to_list(kk)), fxv(vv, V.WVal{}), fxv(rr, V.WObj{})}
    case V.JBind{src, +nn, vv, rr} V.WObj{}:
      V.JPair{M2.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn)))), fxv(vv, V.WVal{}), fxv(rr, V.WObj{})}
    case other _:
      other

# tj_fx for an array cell, by what follows it
law tj_fx_cons:
  for tl: V.Json
  for +hd: V.Json
  for ih_hd: {M2.tj(hd, V.WVal{}) == M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}) : List<&2, Lex.Tok>}
  for ih_tl: {M2.tj(tl, V.WArr{}) == M4.tj_r(fxv(tl, V.WArr{}), V.WArr{}) : List<&2, Lex.Tok>}
  {M2.tj(V.JCons{hd, tl}, V.WArr{}) == M4.tj_r(fxv(V.JCons{hd, tl}, V.WArr{}), V.WArr{}) : List<&2, Lex.Tok>}

def tj_fx_cons(tl, hd, ih_hd, ih_tl):
  match tl:
    case V.JNull{}:
      Equal.trans(List<&2, Lex.Tok>, List.append(&2, Lex.Tok, M2.tj(hd, V.WVal{}), Lex.TComma{} <> M2.tj(V.JNull{},
        V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}), Lex.TComma{} <> M2.tj(V.JNull{},
        V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}),
            Lex.TComma{} <> M4.tj_r(fxv(V.JNull{},
        V.WArr{}), V.WArr{})), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.append(&2, Lex.Tok, zz,
        Lex.TComma{} <> M2.tj(V.JNull{}, V.WArr{})), M2.tj(hd, V.WVal{}), M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}), ih_hd),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JNull{}, V.WArr{}), M4.tj_r(fxv(V.JNull{}, V.WArr{}), V.WArr{}), ih_tl))
    case V.JBool{+b1}:
      Equal.trans(List<&2, Lex.Tok>, List.append(&2, Lex.Tok, M2.tj(hd, V.WVal{}), Lex.TComma{} <> M2.tj(V.JBool{b1},
        V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}), Lex.TComma{} <> M2.tj(V.JBool{b1},
        V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}),
            Lex.TComma{} <> M4.tj_r(fxv(V.JBool{b1},
        V.WArr{}), V.WArr{})), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.append(&2, Lex.Tok, zz,
        Lex.TComma{} <> M2.tj(V.JBool{b1}, V.WArr{})), M2.tj(hd, V.WVal{}), M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}),
            ih_hd),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JBool{b1}, V.WArr{}), M4.tj_r(fxv(V.JBool{b1}, V.WArr{}), V.WArr{}),
            ih_tl))
    case V.JNum{+b1}:
      Equal.trans(List<&2, Lex.Tok>, List.append(&2, Lex.Tok, M2.tj(hd, V.WVal{}), Lex.TComma{} <> M2.tj(V.JNum{b1},
        V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}), Lex.TComma{} <> M2.tj(V.JNum{b1},
        V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}),
            Lex.TComma{} <> M4.tj_r(fxv(V.JNum{b1},
        V.WArr{}), V.WArr{})), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.append(&2, Lex.Tok, zz,
        Lex.TComma{} <> M2.tj(V.JNum{b1}, V.WArr{})), M2.tj(hd, V.WVal{}), M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}), ih_hd),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JNum{b1}, V.WArr{}), M4.tj_r(fxv(V.JNum{b1}, V.WArr{}), V.WArr{}),
            ih_tl))
    case V.JStr{+b1}:
      Equal.trans(List<&2, Lex.Tok>, List.append(&2, Lex.Tok, M2.tj(hd, V.WVal{}), Lex.TComma{} <> M2.tj(V.JStr{b1},
        V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}), Lex.TComma{} <> M2.tj(V.JStr{b1},
        V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}),
            Lex.TComma{} <> M4.tj_r(fxv(V.JStr{b1},
        V.WArr{}), V.WArr{})), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.append(&2, Lex.Tok, zz,
        Lex.TComma{} <> M2.tj(V.JStr{b1}, V.WArr{})), M2.tj(hd, V.WVal{}), M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}), ih_hd),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JStr{b1}, V.WArr{}), M4.tj_r(fxv(V.JStr{b1}, V.WArr{}), V.WArr{}),
            ih_tl))
    case V.JArr{+b1}:
      Equal.trans(List<&2, Lex.Tok>, List.append(&2, Lex.Tok, M2.tj(hd, V.WVal{}), Lex.TComma{} <> M2.tj(V.JArr{b1},
        V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}), Lex.TComma{} <> M2.tj(V.JArr{b1},
        V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}),
            Lex.TComma{} <> M4.tj_r(fxv(V.JArr{b1},
        V.WArr{}), V.WArr{})), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.append(&2, Lex.Tok, zz,
        Lex.TComma{} <> M2.tj(V.JArr{b1}, V.WArr{})), M2.tj(hd, V.WVal{}), M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}), ih_hd),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JArr{b1}, V.WArr{}), M4.tj_r(fxv(V.JArr{b1}, V.WArr{}), V.WArr{}),
            ih_tl))
    case V.JObj{+b1}:
      Equal.trans(List<&2, Lex.Tok>, List.append(&2, Lex.Tok, M2.tj(hd, V.WVal{}), Lex.TComma{} <> M2.tj(V.JObj{b1},
        V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}), Lex.TComma{} <> M2.tj(V.JObj{b1},
        V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}),
            Lex.TComma{} <> M4.tj_r(fxv(V.JObj{b1},
        V.WArr{}), V.WArr{})), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.append(&2, Lex.Tok, zz,
        Lex.TComma{} <> M2.tj(V.JObj{b1}, V.WArr{})), M2.tj(hd, V.WVal{}), M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}), ih_hd),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JObj{b1}, V.WArr{}), M4.tj_r(fxv(V.JObj{b1}, V.WArr{}), V.WArr{}),
            ih_tl))
    case V.JNil{}:
      ih_hd
    case V.JCons{+b1, +b2}:
      Equal.trans(List<&2, Lex.Tok>, List.append(&2, Lex.Tok, M2.tj(hd, V.WVal{}), Lex.TComma{} <> M2.tj(V.JCons{b1,
          b2},
        V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}), Lex.TComma{} <> M2.tj(V.JCons{b1,
            b2},
        V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}),
            Lex.TComma{} <> M4.tj_r(fxv(V.JCons{b1,
        b2}, V.WArr{}), V.WArr{})), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.append(&2, Lex.Tok, zz,
        Lex.TComma{} <> M2.tj(V.JCons{b1, b2}, V.WArr{})), M2.tj(hd, V.WVal{}), M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}),
            ih_hd),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JCons{b1, b2}, V.WArr{}), M4.tj_r(fxv(V.JCons{b1, b2}, V.WArr{}),
            V.WArr{}),
        ih_tl))
    case V.JPair{+b1, +b2, +b3}:
      Equal.trans(List<&2, Lex.Tok>, List.append(&2, Lex.Tok, M2.tj(hd, V.WVal{}), Lex.TComma{} <> M2.tj(V.JPair{b1,
          b2, b3},
        V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}), Lex.TComma{} <> M2.tj(V.JPair{b1,
            b2, b3},
        V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}),
            Lex.TComma{} <> M4.tj_r(fxv(V.JPair{b1,
        b2, b3}, V.WArr{}), V.WArr{})), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.append(&2, Lex.Tok,
        zz, Lex.TComma{} <> M2.tj(V.JPair{b1, b2, b3}, V.WArr{})), M2.tj(hd, V.WVal{}), M4.tj_r(fxv(hd, V.WVal{}),
            V.WVal{}),
        ih_hd), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.append(&2, Lex.Tok, M4.tj_r(fxv(hd,
            V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JPair{b1, b2, b3}, V.WArr{}), M4.tj_r(fxv(V.JPair{b1, b2, b3},
            V.WArr{}),
        V.WArr{}), ih_tl))
    case V.JSpan{+b1, +b2}:
      Equal.trans(List<&2, Lex.Tok>, List.append(&2, Lex.Tok, M2.tj(hd, V.WVal{}), Lex.TComma{} <> M2.tj(V.JSpan{b1,
          b2},
        V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}), Lex.TComma{} <> M2.tj(V.JSpan{b1,
            b2},
        V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}),
            Lex.TComma{} <> M4.tj_r(fxv(V.JSpan{b1,
        b2}, V.WArr{}), V.WArr{})), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.append(&2, Lex.Tok, zz,
        Lex.TComma{} <> M2.tj(V.JSpan{b1, b2}, V.WArr{})), M2.tj(hd, V.WVal{}), M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}),
            ih_hd),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JSpan{b1, b2}, V.WArr{}), M4.tj_r(fxv(V.JSpan{b1, b2}, V.WArr{}),
            V.WArr{}),
        ih_tl))
    case V.JBind{+b1, +b2, +b3, +b4}:
      Equal.trans(List<&2, Lex.Tok>, List.append(&2, Lex.Tok, M2.tj(hd, V.WVal{}), Lex.TComma{} <> M2.tj(V.JBind{b1,
          b2, b3,
        b4}, V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}),
            Lex.TComma{} <> M2.tj(V.JBind{b1, b2,
        b3, b4}, V.WArr{})), List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M4.tj_r(fxv(V.JBind{b1, b2, b3, b4}, V.WArr{}), V.WArr{})), Equal.cong(List<&2, Lex.Tok>,
            List<&2,
        Lex.Tok>, zz => List.append(&2, Lex.Tok, zz, Lex.TComma{} <> M2.tj(V.JBind{b1, b2, b3, b4}, V.WArr{})),
            M2.tj(hd,
        V.WVal{}), M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}), ih_hd), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => List.append(&2, Lex.Tok, M4.tj_r(fxv(hd, V.WVal{}), V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JBind{b1, b2,
            b3,
        b4}, V.WArr{}), M4.tj_r(fxv(V.JBind{b1, b2, b3, b4}, V.WArr{}), V.WArr{}), ih_tl))

# tj_fx for an object cell, by what follows it
law tj_fx_pair:
  for rr: V.Json
  for +kk: String
  for +vv: V.Json
  for ih_v: {M2.tj(vv, V.WVal{}) == M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}) : List<&2, Lex.Tok>}
  for ih_r: {M2.tj(rr, V.WObj{}) == M4.tj_r(fxv(rr, V.WObj{}), V.WObj{}) : List<&2, Lex.Tok>}
  {M2.tj(V.JPair{kk, vv, rr}, V.WObj{}) == M4.tj_r(fxv(V.JPair{kk, vv, rr}, V.WObj{}), V.WObj{}) : List<&2, Lex.Tok>}

def tj_fx_pair(rr, kk, vv, ih_v, ih_r):
  match rr:
    case V.JNull{}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
        M2.tj(vv, V.WVal{}), Lex.TComma{} <> M2.tj(V.JNull{}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M2.tj(V.JNull{}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M4.tj_r(fxv(V.JNull{}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>, List<&2,
        Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, zz,
        Lex.TComma{} <> M2.tj(V.JNull{}, V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}), ih_v),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv,
            V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JNull{}, V.WObj{}), M4.tj_r(fxv(V.JNull{}, V.WObj{}), V.WObj{}), ih_r))
    case V.JBool{+b1}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
        M2.tj(vv, V.WVal{}), Lex.TComma{} <> M2.tj(V.JBool{b1}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M2.tj(V.JBool{b1}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M4.tj_r(fxv(V.JBool{b1}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>,
            List<&2,
        Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, zz,
        Lex.TComma{} <> M2.tj(V.JBool{b1}, V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}), ih_v),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv,
            V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JBool{b1}, V.WObj{}), M4.tj_r(fxv(V.JBool{b1}, V.WObj{}), V.WObj{}),
            ih_r))
    case V.JNum{+b1}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
        M2.tj(vv, V.WVal{}), Lex.TComma{} <> M2.tj(V.JNum{b1}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M2.tj(V.JNum{b1}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M4.tj_r(fxv(V.JNum{b1}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>, List<&2,
        Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, zz,
        Lex.TComma{} <> M2.tj(V.JNum{b1}, V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}), ih_v),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv,
            V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JNum{b1}, V.WObj{}), M4.tj_r(fxv(V.JNum{b1}, V.WObj{}), V.WObj{}),
            ih_r))
    case V.JStr{+b1}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
        M2.tj(vv, V.WVal{}), Lex.TComma{} <> M2.tj(V.JStr{b1}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M2.tj(V.JStr{b1}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M4.tj_r(fxv(V.JStr{b1}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>, List<&2,
        Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, zz,
        Lex.TComma{} <> M2.tj(V.JStr{b1}, V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}), ih_v),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv,
            V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JStr{b1}, V.WObj{}), M4.tj_r(fxv(V.JStr{b1}, V.WObj{}), V.WObj{}),
            ih_r))
    case V.JArr{+b1}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
        M2.tj(vv, V.WVal{}), Lex.TComma{} <> M2.tj(V.JArr{b1}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M2.tj(V.JArr{b1}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M4.tj_r(fxv(V.JArr{b1}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>, List<&2,
        Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, zz,
        Lex.TComma{} <> M2.tj(V.JArr{b1}, V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}), ih_v),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv,
            V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JArr{b1}, V.WObj{}), M4.tj_r(fxv(V.JArr{b1}, V.WObj{}), V.WObj{}),
            ih_r))
    case V.JObj{+b1}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
        M2.tj(vv, V.WVal{}), Lex.TComma{} <> M2.tj(V.JObj{b1}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M2.tj(V.JObj{b1}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M4.tj_r(fxv(V.JObj{b1}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>, List<&2,
        Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, zz,
        Lex.TComma{} <> M2.tj(V.JObj{b1}, V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}), ih_v),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv,
            V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JObj{b1}, V.WObj{}), M4.tj_r(fxv(V.JObj{b1}, V.WObj{}), V.WObj{}),
            ih_r))
    case V.JNil{}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
          zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> zz,
        M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}), ih_v)
    case V.JCons{+b1, +b2}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
        M2.tj(vv, V.WVal{}), Lex.TComma{} <> M2.tj(V.JCons{b1, b2}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M2.tj(V.JCons{b1, b2}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M4.tj_r(fxv(V.JCons{b1, b2}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>,
        List<&2, Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, zz,
        Lex.TComma{} <> M2.tj(V.JCons{b1, b2}, V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
            ih_v),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv,
            V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JCons{b1, b2}, V.WObj{}), M4.tj_r(fxv(V.JCons{b1, b2}, V.WObj{}),
            V.WObj{}),
        ih_r))
    case V.JPair{+b1, +b2, +b3}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
        M2.tj(vv, V.WVal{}), Lex.TComma{} <> M2.tj(V.JPair{b1, b2, b3}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M2.tj(V.JPair{b1, b2, b3}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M4.tj_r(fxv(V.JPair{b1, b2, b3}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>,
        List<&2, Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, zz,
        Lex.TComma{} <> M2.tj(V.JPair{b1, b2, b3}, V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}),
            V.WVal{}), ih_v),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv,
            V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JPair{b1, b2, b3}, V.WObj{}), M4.tj_r(fxv(V.JPair{b1, b2, b3},
            V.WObj{}),
        V.WObj{}), ih_r))
    case V.JSpan{+b1, +b2}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
        M2.tj(vv, V.WVal{}), Lex.TComma{} <> M2.tj(V.JSpan{b1, b2}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M2.tj(V.JSpan{b1, b2}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M4.tj_r(fxv(V.JSpan{b1, b2}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>,
        List<&2, Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, zz,
        Lex.TComma{} <> M2.tj(V.JSpan{b1, b2}, V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
            ih_v),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv,
            V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JSpan{b1, b2}, V.WObj{}), M4.tj_r(fxv(V.JSpan{b1, b2}, V.WObj{}),
            V.WObj{}),
        ih_r))
    case V.JBind{+b1, +b2, +b3, +b4}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
        M2.tj(vv, V.WVal{}), Lex.TComma{} <> M2.tj(V.JBind{b1, b2, b3, b4}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M2.tj(V.JBind{b1, b2, b3, b4}, V.WObj{})),
        Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}),
        V.WVal{}), Lex.TComma{} <> M4.tj_r(fxv(V.JBind{b1, b2, b3, b4}, V.WObj{}), V.WObj{})), Equal.cong(List<&2,
        Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2,
        Lex.Tok, zz, Lex.TComma{} <> M2.tj(V.JBind{b1, b2, b3, b4}, V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv,
            V.WVal{}),
        V.WVal{}), ih_v), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TStr{M2.fixs(String.to_list(kk))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv,
            V.WVal{}),
        V.WVal{}), Lex.TComma{} <> zz), M2.tj(V.JBind{b1, b2, b3, b4}, V.WObj{}), M4.tj_r(fxv(V.JBind{b1, b2, b3, b4},
        V.WObj{}), V.WObj{}), ih_r))

# tj_fx for an object cell, by what follows it
law tj_fx_bind:
  for rr: V.Json
  for +src: String
  for +nn: U32
  for +vv: V.Json
  for ih_v: {M2.tj(vv, V.WVal{}) == M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}) : List<&2, Lex.Tok>}
  for ih_r: {M2.tj(rr, V.WObj{}) == M4.tj_r(fxv(rr, V.WObj{}), V.WObj{}) : List<&2, Lex.Tok>}
  {M2.tj(V.JBind{src, nn, vv, rr}, V.WObj{}) == M4.tj_r(fxv(V.JBind{src, nn, vv, rr}, V.WObj{}), V.WObj{}) : List<&2,
    Lex.Tok>}

def tj_fx_bind(rr, src, nn, vv, ih_v, ih_r):
  match rr:
    case V.JNull{}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M2.tj(vv, V.WVal{}),
            Lex.TComma{} <> M2.tj(V.JNull{},
        V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JNull{}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M4.tj_r(fxv(V.JNull{}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2,
        Lex.Tok, zz, Lex.TComma{} <> M2.tj(V.JNull{}, V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}),
            V.WVal{}),
        ih_v), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src,
            nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> zz), M2.tj(V.JNull{}, V.WObj{}), M4.tj_r(fxv(V.JNull{}, V.WObj{}), V.WObj{}), ih_r))
    case V.JBool{+b1}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M2.tj(vv, V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JBool{b1}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JBool{b1}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M4.tj_r(fxv(V.JBool{b1}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2,
        Lex.Tok, zz, Lex.TComma{} <> M2.tj(V.JBool{b1}, V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}),
            V.WVal{}),
        ih_v), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src,
            nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> zz), M2.tj(V.JBool{b1}, V.WObj{}), M4.tj_r(fxv(V.JBool{b1}, V.WObj{}), V.WObj{}), ih_r))
    case V.JNum{+b1}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M2.tj(vv, V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JNum{b1}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JNum{b1}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M4.tj_r(fxv(V.JNum{b1}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2,
        Lex.Tok, zz, Lex.TComma{} <> M2.tj(V.JNum{b1}, V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}),
            V.WVal{}),
        ih_v), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src,
            nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> zz), M2.tj(V.JNum{b1}, V.WObj{}), M4.tj_r(fxv(V.JNum{b1}, V.WObj{}), V.WObj{}), ih_r))
    case V.JStr{+b1}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M2.tj(vv, V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JStr{b1}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JStr{b1}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M4.tj_r(fxv(V.JStr{b1}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2,
        Lex.Tok, zz, Lex.TComma{} <> M2.tj(V.JStr{b1}, V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}),
            V.WVal{}),
        ih_v), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src,
            nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> zz), M2.tj(V.JStr{b1}, V.WObj{}), M4.tj_r(fxv(V.JStr{b1}, V.WObj{}), V.WObj{}), ih_r))
    case V.JArr{+b1}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M2.tj(vv, V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JArr{b1}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JArr{b1}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M4.tj_r(fxv(V.JArr{b1}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2,
        Lex.Tok, zz, Lex.TComma{} <> M2.tj(V.JArr{b1}, V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}),
            V.WVal{}),
        ih_v), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src,
            nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> zz), M2.tj(V.JArr{b1}, V.WObj{}), M4.tj_r(fxv(V.JArr{b1}, V.WObj{}), V.WObj{}), ih_r))
    case V.JObj{+b1}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M2.tj(vv, V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JObj{b1}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JObj{b1}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M4.tj_r(fxv(V.JObj{b1}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
        zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2,
        Lex.Tok, zz, Lex.TComma{} <> M2.tj(V.JObj{b1}, V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}),
            V.WVal{}),
        ih_v), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src,
            nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> zz), M2.tj(V.JObj{b1}, V.WObj{}), M4.tj_r(fxv(V.JObj{b1}, V.WObj{}), V.WObj{}), ih_r))
    case V.JNil{}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> zz, M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}), ih_v)
    case V.JCons{+b1, +b2}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M2.tj(vv, V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JCons{b1, b2}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JCons{b1, b2}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M4.tj_r(fxv(V.JCons{b1, b2}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>, List<&2,
        Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, zz, Lex.TComma{} <> M2.tj(V.JCons{b1, b2},
        V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}), ih_v), Equal.cong(List<&2, Lex.Tok>,
            List<&2,
        Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> zz), M2.tj(V.JCons{b1, b2}, V.WObj{}), M4.tj_r(fxv(V.JCons{b1, b2}, V.WObj{}), V.WObj{}), ih_r))
    case V.JPair{+b1, +b2, +b3}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M2.tj(vv, V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JPair{b1, b2, b3}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JPair{b1, b2, b3}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M4.tj_r(fxv(V.JPair{b1, b2, b3}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>, List<&2,
        Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, zz, Lex.TComma{} <> M2.tj(V.JPair{b1, b2, b3},
        V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}), ih_v), Equal.cong(List<&2, Lex.Tok>,
            List<&2,
        Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> zz), M2.tj(V.JPair{b1, b2, b3}, V.WObj{}), M4.tj_r(fxv(V.JPair{b1, b2, b3}, V.WObj{}),
            V.WObj{}),
        ih_r))
    case V.JSpan{+b1, +b2}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M2.tj(vv, V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JSpan{b1, b2}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JSpan{b1, b2}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M4.tj_r(fxv(V.JSpan{b1, b2}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>, List<&2,
        Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, zz, Lex.TComma{} <> M2.tj(V.JSpan{b1, b2},
        V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}), ih_v), Equal.cong(List<&2, Lex.Tok>,
            List<&2,
        Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> zz), M2.tj(V.JSpan{b1, b2}, V.WObj{}), M4.tj_r(fxv(V.JSpan{b1, b2}, V.WObj{}), V.WObj{}), ih_r))
    case V.JBind{+b1, +b2, +b3, +b4}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M2.tj(vv, V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JBind{b1, b2, b3, b4}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M2.tj(V.JBind{b1, b2, b3, b4}, V.WObj{})), Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> M4.tj_r(fxv(V.JBind{b1, b2, b3, b4}, V.WObj{}), V.WObj{})), Equal.cong(List<&2, Lex.Tok>,
            List<&2,
        Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, zz, Lex.TComma{} <> M2.tj(V.JBind{b1, b2, b3,
            b4},
        V.WObj{})), M2.tj(vv, V.WVal{}), M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}), ih_v), Equal.cong(List<&2, Lex.Tok>,
            List<&2,
        Lex.Tok>, zz => Lex.TStr{M2.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M4.tj_r(fxv(vv, V.WVal{}), V.WVal{}),
        Lex.TComma{} <> zz), M2.tj(V.JBind{b1, b2, b3, b4}, V.WObj{}), M4.tj_r(fxv(V.JBind{b1, b2, b3, b4}, V.WObj{}),
        V.WObj{}), ih_r))

# whether a shape is not the array cells'
def off_arr(sh: V.Shape) -> Bool:
  match sh:
    case V.WArr{}:
      False{}
    case _:
      True{}

# whether a shape is not the object cells'
def off_obj(sh: V.Shape) -> Bool:
  match sh:
    case V.WObj{}:
      False{}
    case _:
      True{}

# tj_fx for a cell where its shape is not the one it has
law tj_fx_cx:
  for tl: V.Json
  for +hd: V.Json
  for sh: V.Shape
  for h: {off_arr(sh) == True{} : Bool}
  {M2.tj(V.JCons{hd, tl}, sh) == M4.tj_r(fxv(V.JCons{hd, tl}, sh), sh) : List<&2, Lex.Tok>}

def tj_fx_cx(tl, hd, sh, h):
  match tl:
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          M2.no({M2.tj(V.JCons{hd, V.JNull{}}, V.WArr{}) == M4.tj_r(fxv(V.JCons{hd, V.JNull{}}, V.WArr{}),
              V.WArr{}) : List<&2,
            Lex.Tok>}, h)
        case V.WObj{}:
          {==}
    case V.JBool{+b1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          M2.no({M2.tj(V.JCons{hd, V.JBool{b1}}, V.WArr{}) == M4.tj_r(fxv(V.JCons{hd, V.JBool{b1}}, V.WArr{}),
            V.WArr{}) : List<&2, Lex.Tok>}, h)
        case V.WObj{}:
          {==}
    case V.JNum{+b1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          M2.no({M2.tj(V.JCons{hd, V.JNum{b1}}, V.WArr{}) == M4.tj_r(fxv(V.JCons{hd, V.JNum{b1}}, V.WArr{}),
            V.WArr{}) : List<&2, Lex.Tok>}, h)
        case V.WObj{}:
          {==}
    case V.JStr{+b1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          M2.no({M2.tj(V.JCons{hd, V.JStr{b1}}, V.WArr{}) == M4.tj_r(fxv(V.JCons{hd, V.JStr{b1}}, V.WArr{}),
            V.WArr{}) : List<&2, Lex.Tok>}, h)
        case V.WObj{}:
          {==}
    case V.JArr{+b1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          M2.no({M2.tj(V.JCons{hd, V.JArr{b1}}, V.WArr{}) == M4.tj_r(fxv(V.JCons{hd, V.JArr{b1}}, V.WArr{}),
            V.WArr{}) : List<&2, Lex.Tok>}, h)
        case V.WObj{}:
          {==}
    case V.JObj{+b1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          M2.no({M2.tj(V.JCons{hd, V.JObj{b1}}, V.WArr{}) == M4.tj_r(fxv(V.JCons{hd, V.JObj{b1}}, V.WArr{}),
            V.WArr{}) : List<&2, Lex.Tok>}, h)
        case V.WObj{}:
          {==}
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          M2.no({M2.tj(V.JCons{hd, V.JNil{}}, V.WArr{}) == M4.tj_r(fxv(V.JCons{hd, V.JNil{}}, V.WArr{}),
              V.WArr{}) : List<&2,
            Lex.Tok>}, h)
        case V.WObj{}:
          {==}
    case V.JCons{+b1, +b2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          M2.no({M2.tj(V.JCons{hd, V.JCons{b1, b2}}, V.WArr{}) == M4.tj_r(fxv(V.JCons{hd, V.JCons{b1, b2}}, V.WArr{}),
            V.WArr{}) : List<&2, Lex.Tok>}, h)
        case V.WObj{}:
          {==}
    case V.JPair{+b1, +b2, +b3}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          M2.no({M2.tj(V.JCons{hd, V.JPair{b1, b2, b3}}, V.WArr{}) == M4.tj_r(fxv(V.JCons{hd, V.JPair{b1, b2, b3}},
              V.WArr{}),
            V.WArr{}) : List<&2, Lex.Tok>}, h)
        case V.WObj{}:
          {==}
    case V.JSpan{+b1, +b2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          M2.no({M2.tj(V.JCons{hd, V.JSpan{b1, b2}}, V.WArr{}) == M4.tj_r(fxv(V.JCons{hd, V.JSpan{b1, b2}}, V.WArr{}),
            V.WArr{}) : List<&2, Lex.Tok>}, h)
        case V.WObj{}:
          {==}
    case V.JBind{+b1, +b2, +b3, +b4}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          M2.no({M2.tj(V.JCons{hd, V.JBind{b1, b2, b3, b4}}, V.WArr{}) == M4.tj_r(fxv(V.JCons{hd, V.JBind{b1, b2, b3,
              b4}},
            V.WArr{}), V.WArr{}) : List<&2, Lex.Tok>}, h)
        case V.WObj{}:
          {==}

# tj_fx for a cell where its shape is not the one it has
law tj_fx_px:
  for rr: V.Json
  for +kk: String
  for +vv: V.Json
  for sh: V.Shape
  for h: {off_obj(sh) == True{} : Bool}
  {M2.tj(V.JPair{kk, vv, rr}, sh) == M4.tj_r(fxv(V.JPair{kk, vv, rr}, sh), sh) : List<&2, Lex.Tok>}

def tj_fx_px(rr, kk, vv, sh, h):
  match rr:
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JPair{kk, vv, V.JNull{}}, V.WObj{}) == M4.tj_r(fxv(V.JPair{kk, vv, V.JNull{}}, V.WObj{}),
            V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JBool{+b1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JPair{kk, vv, V.JBool{b1}}, V.WObj{}) == M4.tj_r(fxv(V.JPair{kk, vv, V.JBool{b1}}, V.WObj{}),
            V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JNum{+b1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JPair{kk, vv, V.JNum{b1}}, V.WObj{}) == M4.tj_r(fxv(V.JPair{kk, vv, V.JNum{b1}}, V.WObj{}),
            V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JStr{+b1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JPair{kk, vv, V.JStr{b1}}, V.WObj{}) == M4.tj_r(fxv(V.JPair{kk, vv, V.JStr{b1}}, V.WObj{}),
            V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JArr{+b1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JPair{kk, vv, V.JArr{b1}}, V.WObj{}) == M4.tj_r(fxv(V.JPair{kk, vv, V.JArr{b1}}, V.WObj{}),
            V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JObj{+b1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JPair{kk, vv, V.JObj{b1}}, V.WObj{}) == M4.tj_r(fxv(V.JPair{kk, vv, V.JObj{b1}}, V.WObj{}),
            V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JPair{kk, vv, V.JNil{}}, V.WObj{}) == M4.tj_r(fxv(V.JPair{kk, vv, V.JNil{}}, V.WObj{}),
            V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JCons{+b1, +b2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JPair{kk, vv, V.JCons{b1, b2}}, V.WObj{}) == M4.tj_r(fxv(V.JPair{kk, vv, V.JCons{b1, b2}},
              V.WObj{}),
            V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JPair{+b1, +b2, +b3}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JPair{kk, vv, V.JPair{b1, b2, b3}}, V.WObj{}) == M4.tj_r(fxv(V.JPair{kk, vv, V.JPair{b1, b2,
              b3}},
            V.WObj{}), V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JSpan{+b1, +b2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JPair{kk, vv, V.JSpan{b1, b2}}, V.WObj{}) == M4.tj_r(fxv(V.JPair{kk, vv, V.JSpan{b1, b2}},
              V.WObj{}),
            V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JBind{+b1, +b2, +b3, +b4}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JPair{kk, vv, V.JBind{b1, b2, b3, b4}}, V.WObj{}) == M4.tj_r(fxv(V.JPair{kk, vv, V.JBind{b1,
              b2, b3,
            b4}}, V.WObj{}), V.WObj{}) : List<&2, Lex.Tok>}, h)

# tj_fx for a cell where its shape is not the one it has
law tj_fx_bx:
  for rr: V.Json
  for +src: String
  for +nn: U32
  for +vv: V.Json
  for sh: V.Shape
  for h: {off_obj(sh) == True{} : Bool}
  {M2.tj(V.JBind{src, nn, vv, rr}, sh) == M4.tj_r(fxv(V.JBind{src, nn, vv, rr}, sh), sh) : List<&2, Lex.Tok>}

def tj_fx_bx(rr, src, nn, vv, sh, h):
  match rr:
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JBind{src, nn, vv, V.JNull{}}, V.WObj{}) == M4.tj_r(fxv(V.JBind{src, nn, vv, V.JNull{}},
              V.WObj{}),
            V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JBool{+b1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JBind{src, nn, vv, V.JBool{b1}}, V.WObj{}) == M4.tj_r(fxv(V.JBind{src, nn, vv, V.JBool{b1}},
              V.WObj{}),
            V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JNum{+b1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JBind{src, nn, vv, V.JNum{b1}}, V.WObj{}) == M4.tj_r(fxv(V.JBind{src, nn, vv, V.JNum{b1}},
              V.WObj{}),
            V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JStr{+b1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JBind{src, nn, vv, V.JStr{b1}}, V.WObj{}) == M4.tj_r(fxv(V.JBind{src, nn, vv, V.JStr{b1}},
              V.WObj{}),
            V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JArr{+b1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JBind{src, nn, vv, V.JArr{b1}}, V.WObj{}) == M4.tj_r(fxv(V.JBind{src, nn, vv, V.JArr{b1}},
              V.WObj{}),
            V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JObj{+b1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JBind{src, nn, vv, V.JObj{b1}}, V.WObj{}) == M4.tj_r(fxv(V.JBind{src, nn, vv, V.JObj{b1}},
              V.WObj{}),
            V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JBind{src, nn, vv, V.JNil{}}, V.WObj{}) == M4.tj_r(fxv(V.JBind{src, nn, vv, V.JNil{}},
              V.WObj{}),
            V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JCons{+b1, +b2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JBind{src, nn, vv, V.JCons{b1, b2}}, V.WObj{}) == M4.tj_r(fxv(V.JBind{src, nn, vv, V.JCons{b1,
              b2}},
            V.WObj{}), V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JPair{+b1, +b2, +b3}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JBind{src, nn, vv, V.JPair{b1, b2, b3}}, V.WObj{}) == M4.tj_r(fxv(V.JBind{src, nn, vv,
              V.JPair{b1, b2,
            b3}}, V.WObj{}), V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JSpan{+b1, +b2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JBind{src, nn, vv, V.JSpan{b1, b2}}, V.WObj{}) == M4.tj_r(fxv(V.JBind{src, nn, vv, V.JSpan{b1,
              b2}},
            V.WObj{}), V.WObj{}) : List<&2, Lex.Tok>}, h)
    case V.JBind{+b1, +b2, +b3, +b4}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          M2.no({M2.tj(V.JBind{src, nn, vv, V.JBind{b1, b2, b3, b4}}, V.WObj{}) == M4.tj_r(fxv(V.JBind{src, nn, vv,
              V.JBind{b1,
            b2, b3, b4}}, V.WObj{}), V.WObj{}) : List<&2, Lex.Tok>}, h)

# a value's tokens are those of its strings fixed
law tj_fx:
  for +val: V.Json
  for +sh: V.Shape
  {M2.tj(val, sh) == M4.tj_r(fxv(val, sh), sh) : List<&2, Lex.Tok>}

def tj_fx(val, sh):
  match val:
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JBool{True{}}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JBool{False{}}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JNum{+a1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JStr{+a1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JArr{+a1}:
      match sh:
        case V.WVal{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TOpenArr{} <> List.append(&2, Lex.Tok, zz,
            [Lex.TCloseArr{}]), M2.tj(a1, V.WArr{}), M4.tj_r(fxv(a1, V.WArr{}), V.WArr{}), tj_fx(a1, V.WArr{}))
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JObj{+a1}:
      match sh:
        case V.WVal{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TOpenObj{} <> List.append(&2, Lex.Tok, zz,
            [Lex.TCloseObj{}]), M2.tj(a1, V.WObj{}), M4.tj_r(fxv(a1, V.WObj{}), V.WObj{}), tj_fx(a1, V.WObj{}))
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JCons{+a1, +a2}:
      match sh:
        case V.WVal{}:
          tj_fx_cx(a2, a1, V.WVal{}, {==})
        case V.WArr{}:
          tj_fx_cons(a2, a1, tj_fx(a1, V.WVal{}), tj_fx(a2, V.WArr{}))
        case V.WObj{}:
          tj_fx_cx(a2, a1, V.WObj{}, {==})
    case V.JPair{+a1, +a2, +a3}:
      match sh:
        case V.WVal{}:
          tj_fx_px(a3, a1, a2, V.WVal{}, {==})
        case V.WArr{}:
          tj_fx_px(a3, a1, a2, V.WArr{}, {==})
        case V.WObj{}:
          tj_fx_pair(a3, a1, a2, tj_fx(a2, V.WVal{}), tj_fx(a3, V.WObj{}))
    case V.JSpan{+a1, +a2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JBind{+a1, +a2, +a3, +a4}:
      match sh:
        case V.WVal{}:
          tj_fx_bx(a4, a1, a2, a3, V.WVal{}, {==})
        case V.WArr{}:
          tj_fx_bx(a4, a1, a2, a3, V.WArr{}, {==})
        case V.WObj{}:
          tj_fx_bind(a4, a1, a2, a3, tj_fx(a3, V.WVal{}), tj_fx(a4, V.WObj{}))

# dens_tj for a boolean
law dens_bool_r:
  for bb: Bool
  for sh: V.Shape
  {M2.dens(M4.tj_r(V.JBool{bb}, sh)) == M4.tj_r(V.JBool{bb}, sh) : List<&2, Lex.Tok>}

def dens_bool_r(bb, sh):
  match bb:
    case True{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case False{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}

# dens_tj for an array cell, by what follows it
law dens_cons_r:
  for tl: V.Json
  for sh: V.Shape
  for +hd: V.Json
  for ih_hd: {M2.dens(M4.tj_r(hd, V.WVal{})) == M4.tj_r(hd, V.WVal{}) : List<&2, Lex.Tok>}
  for ih_tl: {M2.dens(M4.tj_r(tl, V.WArr{})) == M4.tj_r(tl, V.WArr{}) : List<&2, Lex.Tok>}
  {M2.dens(M4.tj_r(V.JCons{hd, tl}, sh)) == M4.tj_r(V.JCons{hd, tl}, sh) : List<&2, Lex.Tok>}

def dens_cons_r(tl, sh, hd, ih_hd, ih_tl):
  match tl:
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          ih_hd
        case V.WObj{}:
          {==}
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(M4.tj_r(hd, V.WVal{}), M4.tj_r(V.JNull{}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}
    case V.JBool{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(M4.tj_r(hd, V.WVal{}), M4.tj_r(V.JBool{t1}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}
    case V.JNum{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(M4.tj_r(hd, V.WVal{}), M4.tj_r(V.JNum{t1}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}
    case V.JStr{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(M4.tj_r(hd, V.WVal{}), M4.tj_r(V.JStr{t1}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}
    case V.JArr{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(M4.tj_r(hd, V.WVal{}), M4.tj_r(V.JArr{t1}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}
    case V.JObj{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(M4.tj_r(hd, V.WVal{}), M4.tj_r(V.JObj{t1}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}
    case V.JCons{+t1, +t2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(M4.tj_r(hd, V.WVal{}), M4.tj_r(V.JCons{t1, t2}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}
    case V.JPair{+t1, +t2, +t3}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(M4.tj_r(hd, V.WVal{}), M4.tj_r(V.JPair{t1, t2, t3}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}
    case V.JSpan{+t1, +t2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(M4.tj_r(hd, V.WVal{}), M4.tj_r(V.JSpan{t1, t2}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}
    case V.JBind{+t1, +t2, +t3, +t4}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          dens_sep(M4.tj_r(hd, V.WVal{}), M4.tj_r(V.JBind{t1, t2, t3, t4}, V.WArr{}), ih_hd, ih_tl)
        case V.WObj{}:
          {==}

# dens_tj for an object cell, by what follows it
law dens_pair_r:
  for rr: V.Json
  for sh: V.Shape
  for +kk: String
  for +vv: V.Json
  for ih_v: {M2.dens(M4.tj_r(vv, V.WVal{})) == M4.tj_r(vv, V.WVal{}) : List<&2, Lex.Tok>}
  for ih_r: {M2.dens(M4.tj_r(rr, V.WObj{})) == M4.tj_r(rr, V.WObj{}) : List<&2, Lex.Tok>}
  {M2.dens(M4.tj_r(V.JPair{kk, vv, rr}, sh)) == M4.tj_r(V.JPair{kk, vv, rr}, sh) : List<&2, Lex.Tok>}

def dens_pair_r(rr, sh, kk, vv, ih_v, ih_r):
  match rr:
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{kk} <> Lex.TColon{} <> yy, M2.dens(M4.tj_r(vv, V.WVal{})), M4.tj_r(vv,
            V.WVal{}), ih_v)
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{kk} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv,
            V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JNull{}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JNull{}, V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JNull{}, V.WObj{}), ih_v, ih_r))
    case V.JBool{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{kk} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv,
            V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JBool{t1}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JBool{t1}, V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JBool{t1}, V.WObj{}), ih_v, ih_r))
    case V.JNum{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{kk} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv,
            V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JNum{t1}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JNum{t1}, V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JNum{t1}, V.WObj{}), ih_v, ih_r))
    case V.JStr{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{kk} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv,
            V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JStr{t1}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JStr{t1}, V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JStr{t1}, V.WObj{}), ih_v, ih_r))
    case V.JArr{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{kk} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv,
            V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JArr{t1}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JArr{t1}, V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JArr{t1}, V.WObj{}), ih_v, ih_r))
    case V.JObj{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{kk} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv,
            V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JObj{t1}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JObj{t1}, V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JObj{t1}, V.WObj{}), ih_v, ih_r))
    case V.JCons{+t1, +t2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{kk} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv,
            V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JCons{t1,
            t2}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JCons{t1, t2},
              V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JCons{t1, t2}, V.WObj{}), ih_v, ih_r))
    case V.JPair{+t1, +t2, +t3}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{kk} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv,
            V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JPair{t1, t2,
            t3}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JPair{t1, t2,
                t3},
              V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JPair{t1, t2, t3}, V.WObj{}), ih_v, ih_r))
    case V.JSpan{+t1, +t2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{kk} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv,
            V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JSpan{t1,
            t2}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JSpan{t1, t2},
              V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JSpan{t1, t2}, V.WObj{}), ih_v, ih_r))
    case V.JBind{+t1, +t2, +t3, +t4}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
            yy => Lex.TStr{kk} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv,
            V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JBind{t1, t2, t3,
            t4}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}), Lex.TComma{} <> M4.tj_r(V.JBind{t1, t2,
                t3, t4},
              V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JBind{t1, t2, t3, t4}, V.WObj{}), ih_v, ih_r))

# dens_tj for an object cell, by what follows it
law dens_bind_r:
  for rr: V.Json
  for sh: V.Shape
  for +src: String
  for +nn: U32
  for +vv: V.Json
  for ih_v: {M2.dens(M4.tj_r(vv, V.WVal{})) == M4.tj_r(vv, V.WVal{}) : List<&2, Lex.Tok>}
  for ih_r: {M2.dens(M4.tj_r(rr, V.WObj{})) == M4.tj_r(rr, V.WObj{}) : List<&2, Lex.Tok>}
  {M2.dens(M4.tj_r(V.JBind{src, nn, vv, rr}, sh)) == M4.tj_r(V.JBind{src, nn, vv, rr}, sh) : List<&2, Lex.Tok>}

def dens_bind_r(rr, sh, src, nn, vv, ih_v, ih_r):
  match rr:
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{V.span.str(src, nn,
            U32.is_zero(nn))} <> Lex.TColon{} <> yy, M2.dens(M4.tj_r(vv, V.WVal{})), M4.tj_r(vv, V.WVal{}), ih_v)
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{V.span.str(src, nn,
            U32.is_zero(nn))} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JNull{}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JNull{}, V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JNull{}, V.WObj{}), ih_v, ih_r))
    case V.JBool{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{V.span.str(src, nn,
            U32.is_zero(nn))} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JBool{t1}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JBool{t1}, V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JBool{t1}, V.WObj{}), ih_v, ih_r))
    case V.JNum{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{V.span.str(src, nn,
            U32.is_zero(nn))} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JNum{t1}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JNum{t1}, V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JNum{t1}, V.WObj{}), ih_v, ih_r))
    case V.JStr{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{V.span.str(src, nn,
            U32.is_zero(nn))} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JStr{t1}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JStr{t1}, V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JStr{t1}, V.WObj{}), ih_v, ih_r))
    case V.JArr{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{V.span.str(src, nn,
            U32.is_zero(nn))} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JArr{t1}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JArr{t1}, V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JArr{t1}, V.WObj{}), ih_v, ih_r))
    case V.JObj{+t1}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{V.span.str(src, nn,
            U32.is_zero(nn))} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JObj{t1}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JObj{t1}, V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JObj{t1}, V.WObj{}), ih_v, ih_r))
    case V.JCons{+t1, +t2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{V.span.str(src, nn,
            U32.is_zero(nn))} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JCons{t1, t2}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JCons{t1, t2}, V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JCons{t1, t2}, V.WObj{}), ih_v, ih_r))
    case V.JPair{+t1, +t2, +t3}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{V.span.str(src, nn,
            U32.is_zero(nn))} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JPair{t1, t2, t3}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JPair{t1, t2, t3}, V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JPair{t1, t2, t3}, V.WObj{}), ih_v, ih_r))
    case V.JSpan{+t1, +t2}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{V.span.str(src, nn,
            U32.is_zero(nn))} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JSpan{t1, t2}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JSpan{t1, t2}, V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JSpan{t1, t2}, V.WObj{}), ih_v, ih_r))
    case V.JBind{+t1, +t2, +t3, +t4}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TStr{V.span.str(src, nn,
            U32.is_zero(nn))} <> Lex.TColon{} <> yy, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(vv, V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JBind{t1, t2, t3, t4}, V.WObj{}))), List.append(&2, Lex.Tok, M4.tj_r(vv,
                  V.WVal{}),
              Lex.TComma{} <> M4.tj_r(V.JBind{t1, t2, t3, t4}, V.WObj{})),
            dens_sep(M4.tj_r(vv, V.WVal{}), M4.tj_r(V.JBind{t1, t2, t3, t4}, V.WObj{}), ih_v, ih_r))

# a value's tokens hold no spans
law dens_tjr:
  for +val: V.Json
  for +sh: V.Shape
  {M2.dens(M4.tj_r(val, sh)) == M4.tj_r(val, sh) : List<&2, Lex.Tok>}

def dens_tjr(val, sh):
  match val:
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JBool{bb}:
      dens_bool_r(bb, sh)
    case V.JNum{raw}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JStr{txt}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JArr{+items}:
      match sh:
        case V.WVal{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TOpenArr{} <> yy, M2.dens(List.append(&2, Lex.Tok,
            M4.tj_r(items, V.WArr{}), [Lex.TCloseArr{}])), List.append(&2, Lex.Tok, M4.tj_r(items, V.WArr{}),
              [Lex.TCloseArr{}]),
            Equal.trans(List<&2, Lex.Tok>, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(items, V.WArr{}),
                [Lex.TCloseArr{}])),
              List.append(&2, Lex.Tok, M2.dens(M4.tj_r(items, V.WArr{})), [Lex.TCloseArr{}]), List.append(&2, Lex.Tok,
              M4.tj_r(items, V.WArr{}), [Lex.TCloseArr{}]),
              M1.dens_app(M4.tj_r(items, V.WArr{}), [Lex.TCloseArr{}]),
              app_cong(M2.dens(M4.tj_r(items, V.WArr{})), M4.tj_r(items, V.WArr{}), [Lex.TCloseArr{}],
                  [Lex.TCloseArr{}],
                dens_tjr(items, V.WArr{}), {==})))
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JObj{+pairs}:
      match sh:
        case V.WVal{}:
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, yy => Lex.TOpenObj{} <> yy, M2.dens(List.append(&2, Lex.Tok,
            M4.tj_r(pairs, V.WObj{}), [Lex.TCloseObj{}])), List.append(&2, Lex.Tok, M4.tj_r(pairs, V.WObj{}),
              [Lex.TCloseObj{}]),
            Equal.trans(List<&2, Lex.Tok>, M2.dens(List.append(&2, Lex.Tok, M4.tj_r(pairs, V.WObj{}),
                [Lex.TCloseObj{}])),
              List.append(&2, Lex.Tok, M2.dens(M4.tj_r(pairs, V.WObj{})), [Lex.TCloseObj{}]), List.append(&2, Lex.Tok,
              M4.tj_r(pairs, V.WObj{}), [Lex.TCloseObj{}]),
              M1.dens_app(M4.tj_r(pairs, V.WObj{}), [Lex.TCloseObj{}]),
              app_cong(M2.dens(M4.tj_r(pairs, V.WObj{})), M4.tj_r(pairs, V.WObj{}), [Lex.TCloseObj{}],
                  [Lex.TCloseObj{}],
                dens_tjr(pairs, V.WObj{}), {==})))
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JCons{+hd, +tl}:
      dens_cons_r(tl, sh, hd, dens_tjr(hd, V.WVal{}), dens_tjr(tl, V.WArr{}))
    case V.JPair{+kk, +vv, +rr}:
      dens_pair_r(rr, sh, kk, vv, dens_tjr(vv, V.WVal{}), dens_tjr(rr, V.WObj{}))
    case V.JSpan{src, nn}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JBind{+src, +nn, +vv, +rr}:
      dens_bind_r(rr, sh, src, nn, vv, dens_tjr(vv, V.WVal{}), dens_tjr(rr, V.WObj{}))

# a value's tokens are already their den
law dens_tj:
  for +val: V.Json
  for +sh: V.Shape
  {M2.dens(M2.tj(val, sh)) == M2.tj(val, sh) : List<&2, Lex.Tok>}

def dens_tj(val, sh):
  Equal.trans(List<&2, Lex.Tok>, M2.dens(M2.tj(val, sh)), M2.dens(M4.tj_r(fxv(val, sh), sh)), M2.tj(val, sh),
      Equal.cong(List<&2,
    Lex.Tok>, List<&2, Lex.Tok>, zz => M2.dens(zz), M2.tj(val, sh), M4.tj_r(fxv(val, sh), sh), tj_fx(val, sh)),
    Equal.trans(List<&2, Lex.Tok>, M2.dens(M4.tj_r(fxv(val, sh), sh)), M4.tj_r(fxv(val, sh), sh), M2.tj(val, sh),
        dens_tjr(fxv(val,
    sh), sh), Equal.sym(List<&2, Lex.Tok>, M2.tj(val, sh), M4.tj_r(fxv(val, sh), sh), tj_fx(val, sh))))
